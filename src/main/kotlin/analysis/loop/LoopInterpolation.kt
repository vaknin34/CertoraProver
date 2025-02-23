/*
 *     The Certora Prover
 *     Copyright (C) 2025  Certora Ltd.
 *
 *     This program is free software: you can redistribute it and/or modify
 *     it under the terms of the GNU General Public License as published by
 *     the Free Software Foundation, version 3 of the License.
 *
 *     This program is distributed in the hope that it will be useful,
 *     but WITHOUT ANY WARRANTY; without even the implied warranty of
 *     MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *     GNU General Public License for more details.
 *
 *     You should have received a copy of the GNU General Public License
 *     along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

package analysis.loop

import allocator.Allocator
import allocator.GeneratedBy
import analysis.LogicalEquivalence
import analysis.getNaturalLoops
import analysis.maybeNarrow
import analysis.smtblaster.Z3BlasterPool
import parallel.ParallelPool
import tac.MetaKey
import tac.MetaMap
import tac.NBId
import tac.Tag
import utils.`to?`
import vc.data.*
import vc.data.tacexprutil.TACExprFreeVarsCollector
import vc.data.tacexprutil.subsFull
import vc.data.tacexprutil.toSymSet
import java.math.BigInteger

object LoopInterpolation {
    @GeneratedBy(Allocator.Id.ASSUME_GROUP)
    val ASSUME_GROUP : MetaKey<Int> = MetaKey("certora.loop.assumes")

    /**
     * Insert assume statements that explicate loop behavior.
     *
     * Generally we are concerned with the memory effects of a loop, and use
     * a very coarse approximation of the variables mutated by the body of a loop.
     *
     * However, when encoding arrays and the like, we need to know if, after a loop is finished
     * whether some variable is pointed to the end of the array segment; if so then that
     * variable is the next pointer for encoding, i.e., where the next encoded object should be
     * placed.
     *
     * Rather than try to infer this by analyzing the loop mid-decoder/encoder analysis, we instead insert
     * assume statements that are interpreted by the decoder analyses. In particular, this interpolator
     * recognizes loops that follow the following pattern:
     *
     * it = v
     * i = 0
     * while(i < l) {
     *    i += 1;
     *    it += c;
     * }
     * and will generate the following assume:
     * assume (it == v + c * l)
     *
     * When l is the length of an array, v is the array base, and c is the size of array elements, then this allows us
     * to learn that it is indeed the end of the array segment, and thus the next pointer.
     */
    fun interpolateLoopSummaries(p: CoreTACProgram) : CoreTACProgram {
        val graph = p.analysisCache.graph
        val loops = getNaturalLoops(graph)
        val toAssume = mutableMapOf<Pair<NBId, NBId>, Map<TACSymbol.Var, Pair<TACSymbol, TACExpr>>>()
        ParallelPool.allocInScope({ Z3BlasterPool() }) { blaster ->
            val loopSummary = LoopSummarization(blaster = blaster,
                    g = graph,
                    loops = loops
            )
            for(l in loops) {
                val singleSucc = l.body.flatMap {
                    graph.succ(it).filter {
                        it !in l.body
                            // We can ignore revert successors because
                            // from the perspective of the interpolator
                            // those are like assume(false)
                            && it !in graph.cache.revertBlocks
                    }
                }.singleOrNull() ?: continue
                val summ = loopSummary.summarizeLoop(l) ?: continue
                if(summ.isDoLoop) {
                    continue
                }
                val mut = summ.iterationEffect.filter {
                    !it.value.equivSym(it.key)
                }
                val iteratorVar = TACExprFreeVarsCollector.getFreeVars(summ.exitCondition).singleOrNull {
                    it in mut
                } ?: continue
                val targetVar = TACExprFreeVarsCollector.getFreeVars(summ.exitCondition).singleOrNull {
                    it !in mut
                } ?: continue
                val iteratorMut = mut[iteratorVar] ?: continue
                if(!LogicalEquivalence.equiv(listOf(), TACExpr.Vec.Add(
                                iteratorVar.asSym(), 1.toBigInteger().asTACSymbol().asSym()
                        ), iteratorMut, blaster)) {
                    continue
                }
                // initialized to zero?
                val loopStart = graph.elab(l.head).commands.first().ptr
                val nonLoopDef = graph.cache.def.defSitesOf(iteratorVar, loopStart).singleOrNull {
                    it.block !in l.body
                }?.let(graph::elab)?.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>() ?: continue
                check(nonLoopDef.cmd.lhs == iteratorVar)
                if(!nonLoopDef.cmd.rhs.equivSym(BigInteger.ZERO.asTACSymbol())) {
                    continue
                }
                if(!LogicalEquivalence.equiv(listOf(), TACExpr.BinRel.Ge(
                                iteratorVar.asSym(), targetVar.asSym()
                        ), summ.exitCondition, blaster)) {
                    continue
                }
                /*
                   Then we have for(i = 0; i < k; i++) { ... }

                   Iterpolate!
                 */
                val selfAddMutations = mut.mapNotNull {
                    val syms = it.value.subsFull.toSymSet()
                    val canInterpolate = it.key in syms &&
                        it.key != TACKeyword.MEM64.toVar() && /* we don't want the interpolator to work on the freememptr, it can
                        create new reads that will make the freememptr live and generate fresh reads of it.
                        We don't want that! See copying of dynamic arrays of structs from storage to memory,
                        where we have an allocation for the array of pointers and additional allocations for the elements
                        inside the copy loop.
                         */
                        syms.all { fv ->
                            fv !is TACSymbol.Var || fv == it.key || fv !in mut
                        } &&
                            (it.value is TACExpr.Vec.Add) && LogicalEquivalence.equiv(listOf(), it.value, TACExpr.Vec.Add(
                                syms.map { it.asSym() }
                    ), blaster)
                    if(!canInterpolate) {
                        return@mapNotNull null
                    }
                    it.key `to?` syms.singleOrNull { sym ->
                        sym != it.key
                    }?.let {
                        TACExpr.Vec.Mul(
                                targetVar.asSym(), it.asSym()
                        )
                    }
                }.mapNotNull {(key, value) ->
                    key `to?` graph.cache.def.defSitesOf(key, loopStart).singleOrNull {
                                    it.block !in l.body
                                }?.let(graph::elab)?.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.takeIf {
                        it.cmd.rhs is TACExpr.Sym
                    }?.let {seed ->
                        (seed.cmd.rhs as TACExpr.Sym).s to value
                    }
                }.toMap()
                val edge = graph.pred(singleSucc).singleOrNull {
                    it in l.body
                }?.let { pred ->
                    (pred to singleSucc)
                } ?: continue
                // give up, something very weird is happening
                if(edge in toAssume) {
                    return@allocInScope p
                }
                if(selfAddMutations.isNotEmpty()) {
                    toAssume[edge] = selfAddMutations
                }
            }
        }
        return p.patching {
            for((edge, toAssumeMap) in toAssume) {
                val decls = mutableSetOf<TACSymbol.Var>()
                val assumeCmds = run {
                    toAssumeMap.flatMap {
                        val assumeGroupId = Allocator.getFreshId(Allocator.Id.ASSUME_GROUP)
                        val tmp1 = TACSymbol.Var(
                                "assume!${Allocator.getFreshId(Allocator.Id.TEMP_VARIABLE)}",
                                Tag.Bit256
                        )
                        val tmp2 = TACSymbol.Var(
                                "assume!${Allocator.getFreshId(Allocator.Id.TEMP_VARIABLE)}",
                                Tag.Bit256
                        )
                        val tmp3 = TACSymbol.Var(
                                "eq!${Allocator.getFreshId(Allocator.Id.TEMP_VARIABLE)}",
                                Tag.Bool
                        )
                        decls.add(tmp1)
                        decls.add(tmp2)
                        decls.add(tmp3)
                        val meta = MetaMap(
                            ASSUME_GROUP to assumeGroupId
                        )
                        listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = tmp1,
                                rhs = it.value.second,
                                meta = meta
                            ),
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = tmp2,
                                rhs = TACExpr.Vec.Add(
                                    it.value.first.asSym(), tmp1.asSym()
                                ),
                                meta = meta
                            ),
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = tmp3,
                                rhs = TACExpr.BinRel.Eq(
                                    tmp2.asSym(), it.key.asSym()
                                ),
                                meta = meta
                            ),
                            TACCmd.Simple.AssumeCmd(
                                cond = tmp3,
                                meta = meta
                            )
                        )
                    }

                }
                it.insertAlongEdge(edge.first, edge.second, assumeCmds)
                it.addVarDecls(decls)
            }
        }
    }
}
