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

package analysis.opt

import algorithms.dominates
import allocator.Allocator
import analysis.*
import evm.MAX_EVM_UINT256
import tac.Tag
import utils.*
import vc.data.*
import java.util.function.BiConsumer
import java.util.function.BinaryOperator
import java.util.function.Supplier
import java.util.stream.Collector
import java.util.stream.Stream

object FreePointerReadFixer {
    /*
      Find cases where the RHS written as the new value of the free pointer is reused instead
      of reading the FP fresh, replace those with a fresh read.
     */
    fun fixFreePointerRead(p: CoreTACProgram) : CoreTACProgram {
        val live = p.analysisCache.lva
        val dom by lazy {
            p.analysisCache.domination
        }
        infix fun CmdPointer.dominates(x: CmdPointer) = dom.dominates(this, x)

        class Holder(
                var newRead: MutableMap<CmdPointer, TACSymbol.Var> = mutableMapOf(),
                var rewrites: MutableMap<CmdPointer, MutableMap<TACSymbol.Var, TACSymbol.Var>> = mutableMapOf()
        )
        val rewrite = p.parallelLtacStream().filter {
            it.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && it.cmd.lhs == TACKeyword.MEM64.toVar() &&
                    it.cmd.rhs is TACExpr.Sym.Var
        }.map {
            it.enarrow<TACExpr.Sym.Var>()
        }.filter {
            // find those writes whose RHS is still live
            it.exp.s in live.liveVariablesAfter(it.ptr)
        }.map {
            it to p.analysisCache.use.useSitesAfter(pointer = it.ptr, v = it.exp.s)
        }.flatMap { (exp, useSites) ->
            val dominatedUseSites = useSites.filter {
                exp.ptr dominates it
            }
            if(dominatedUseSites.isEmpty()) {
                Stream.empty()
            } else {
                Stream.of(exp to dominatedUseSites)
            }
        }.map { (write, rewriteLocs) ->
            val rewrite = Allocator.getFreshId(Allocator.Id.TEMP_VARIABLE)
            val freshName = TACSymbol.Var("freshRead$rewrite", Tag.Bit256)
            val subst = write.exp.s to freshName
            (write.ptr to freshName) to rewriteLocs.map {
                it to subst
            }
        }.collect(Collector.of(Supplier { ->
            Holder()
        }, BiConsumer { u: Holder, t: Pair<Pair<CmdPointer, TACSymbol.Var>, List<Pair<CmdPointer, Pair<TACSymbol.Var, TACSymbol.Var>>>> ->
            u.newRead[t.first.first] = t.first.second
            t.second.forEach {(where, subst) ->
                u.rewrites.computeIfAbsent(where) { mutableMapOf() }.put(subst.first, subst.second)
            }
        }, BinaryOperator { h1: Holder, h2: Holder ->
            h2.newRead.forEach { t, u ->
                h1.newRead[t] = u
            }
            h2.rewrites.forEach { where, subst ->
                h1.rewrites.computeIfAbsent(where) { mutableMapOf() }.putAll(subst)
            }
            h1
        }))

        return p.patching { patch ->
            rewrite.newRead.forEach { where, newVar ->
                patch.replace(where) { orig ->
                    listOf(
                            orig,
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                    lhs = newVar,
                                    rhs = TACKeyword.MEM64.toVar().asSym()
                            )
                    )
                }
                patch.addVarDecl(newVar)
            }
            rewrite.rewrites.forEach { where, subst ->
                patch.replace(where) { c ->
                    listOf(TACVariableSubstitutor(subst).map(c))
                }
            }
        }
    }

    private val penultimateLengthWrite = PatternDSL.build {
        ((Var - !TACKeyword.MEM64.toVar()).locFirst - 32()).first
    }

    /*
     * Find a missing free pointer write!
     */
    fun addMissingFreePointerWrite(c: CoreTACProgram) : CoreTACProgram {
        val comp = PatternMatcher.compilePattern(
                patt = penultimateLengthWrite,
                graph = c.analysisCache.graph
        )
        return c.patching {
            c.parallelLtacStream().filter {
                it.cmd is TACCmd.Simple.AssigningCmd.ByteStore && it.cmd.value is TACSymbol.Var
            }.map {
                it.narrow<TACCmd.Simple.AssigningCmd.ByteStore>()
            }.mapNotNull {
                it `to?` comp.query(it.cmd.value as TACSymbol.Var, it.wrapped).toNullableResult()
            }.filter { (storeLoc, res) ->
                val subtractOp = (res.first.enarrow<TACExpr.BinOp.Sub>().exp.o2 as? TACExpr.Sym.Var ?: return@filter false).s
                val loc = storeLoc.cmd.loc as? TACSymbol.Var ?: return@filter false
                if(res.first.ptr.block != storeLoc.ptr.block) {
                    return@filter false
                }
                /*
                   What we're subtracting has to be where we're writing as well
                 */
                if(subtractOp !in c.analysisCache.gvn.findCopiesAt(target = res.first.ptr, source = storeLoc.ptr to loc)) {
                    return@filter false
                }
                val d = c.analysisCache.use.useSitesAfter(res.second, res.first.ptr).takeIf {
                    it.isNotEmpty()
                }?.let { d ->
                    d.singleOrNull()?.let(c.analysisCache.graph::elab)?.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.takeIf {
                            val rhs = it.cmd.rhs
                            rhs is TACExpr.Vec.Add && rhs.operandsAreSyms() &&
                                    rhs.ls.any {
                                        it == res.second.asSym()
                                    } && rhs.ls.any {
                                it == 0x1f.toBigInteger().asTACSymbol().asSym()
                            }
                    }?.let {
                        c.analysisCache.use.useSitesAfter(it.cmd.lhs, it.ptr).singleOrNull()
                    }?.let(c.analysisCache.graph::elab)?.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.takeIf andCheck@{
                        val rhs = it.cmd.rhs
                        if(rhs !is TACExpr.BinOp.BWAnd) {
                            return@andCheck false
                        }
                        val lowerMask = MAX_EVM_UINT256.andNot(0x1f.toBigInteger()).asTACSymbol().asSym()
                        rhs.o1 is TACExpr.Sym && rhs.o2 is TACExpr.Sym && (rhs.o1 == lowerMask || rhs.o2 == lowerMask)
                    }?.let {
                        c.analysisCache.use.useSitesAfter(it.cmd.lhs, it.ptr)
                    } ?: d
                } ?: return@filter false
                d.none {
                    c.analysisCache.graph.elab(it).maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.let {
                        it.cmd.lhs == TACKeyword.MEM64.toVar() && it.cmd.rhs is TACExpr.Sym.Var
                    } == true
                }
            }.map {
                it.first.ptr to TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = TACKeyword.MEM64.toVar(),
                        rhs = it.second.second.asSym()
                )
            }.sequential().forEach {(where, toAppend) ->
                it.replace(where) { cmd ->
                    listOf(cmd, toAppend)
                }
            }
        }
    }
}
