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

package instrumentation.transformers

import analysis.*
import utils.`to?`
import utils.mapNotNull
import vc.data.*
import java.math.BigInteger
import java.util.stream.Collectors

object InitializationPointerShift {
    private data class AddKtoFP(
        val addLoc: LTACCmd,
        val readLoc: CmdPointer,
        val const: BigInteger
    )

    private data class Instrument(
        val replaceRHS: LTACCmdView<TACCmd.Simple.AssigningCmd>,
        val holder: TACSymbol.Var,
        val k: BigInteger
    )

    /**
     * Shift pointer computations to occur "closer" to an allocation. If we have
     * x = FP;
     * FP = x + c;
     * ...
     * y = FP
     * FP = y + k;
     * z = x + j;
     *
     * This analysis will shift the definition of z up to immediately after the first allocation
     * (if it is sound to do so).
     *
     * This optimization is necessary to make the initialization analysis happy: it will ignore code that occurs as part
     * of sub-object allocations, and in the above pattern, the initialization for the object allocated in x will "miss"
     * the definition of z, leading to an initialization analysis failure.
     */
    fun shiftPointerComputation(c: CoreTACProgram) : CoreTACProgram {
        val touchedVars = c.analysisCache.variableLookup
        val matcher = PatternMatcher.compilePattern(graph = c.analysisCache.graph, patt = PatternDSL.build {
            (Var { p: TACSymbol.Var, lc: LTACCmd ->
                if(p == TACKeyword.MEM64.toVar()) {
                    PatternMatcher.VariableMatch.Match(lc.ptr)
                } else {
                    PatternMatcher.VariableMatch.Continue
                }
            } + Const).commute.withAction { where, fpRead, const ->
                AddKtoFP(
                    const = const,
                    addLoc = where,
                    readLoc = fpRead
                )
            }
        }, traverseFilter = { it != TACKeyword.MEM64.toVar() })
        val toRewrite = c.parallelLtacStream().filter {
            it.ptr.block !in c.analysisCache.revertBlocks
        }.filter {
            TACKeyword.MEM64.toVar() in touchedVars[it.ptr.block]!!
        }.mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd>()
        }.mapNotNull {
            it `to?` matcher.queryFrom(it).toNullableResult()?.takeIf { (_, read, _) ->
                read.block == it.ptr.block && read.pos < it.ptr.pos
            }
        }.mapNotNull { (def, read) ->
            /*
               We have a defining at location def, defined as [old := FP; ... ;x = old + const]

               where the read of FP is in the same block and comes before def.
               The read location is in read.readLoc, the addition location is in read.addLoc, and the
               added amount is in read.const
             */
            val (addLoc, memRead, k) = read

            val firstWrite =
                /*
                  Get the commands between the read of the free pointer and this definition
                 */
                c.analysisCache.graph.iterateBlock(memRead).takeWhile {
                it.ptr != def.ptr
            }.takeIf { it.isNotEmpty() }?.dropWhile {
                /*
                   Strip off all commands that precede the first free pointer write (if there is one)
                 */
                !(it.cmd is TACCmd.Simple.AssigningCmd && it.cmd.lhs == TACKeyword.MEM64.toVar())
            }?.takeIf {
                    it.isNotEmpty()
            }?.takeIf {
                /*
                   So now we have

                   [fp := exp , ... ]

                   Is there *another* free read (i.e., another allocation?) in the sequent BEFORE our addition? If so, we should try to shift the definition
                   of this variable up, i.e., do we have:

                   [old := fp; ... ; fp := exp, ..., x := fp, ..., y := old + k, ...]

                   where old is the old value of the free pointer read at read.readLo
                 */
                !c.analysisCache.lva.isLiveAfter(it.first().ptr, def.cmd.lhs) && it.none {
                    it.cmd is TACCmd.Simple.AssigningCmd && it.cmd.lhs == def.cmd.lhs
                } && it.asSequence().drop(1).takeWhile {
                    it.ptr != addLoc.ptr
                }.any {
                    it.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && it.cmd.rhs.equivSym(TACKeyword.MEM64)
                }
            }?.get(0) ?: return@mapNotNull null
            /*
                So we now have the following:

                we have read the free pointer (at memRead), which is followed by an update of the free pointer
                (at firstWrite).

                After firstWrite (but before the addition at addLoc that defines def) there is another read of the free pointer
                (assumed to be another allocation).

                Thus, we want to shift the addition of addLoc up to immediately after the free pointer write (and before
                the second read)
             */

            /*
            fpHolder will hold the variable that we are adding to, i.e., the old value of the free pointer after the update
            at freeWrite
             */
            val fpHolder = c.analysisCache.graph.elab(memRead).maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.takeIf {
                it.cmd.rhs.equivSym(TACKeyword.MEM64)
            }?.cmd?.lhs?.takeIf { fpHolder ->
                // make sure this variable is still available at the point we do the first free pointer update (at firstWrite)
                c.analysisCache.graph.iterateBlock(memRead).asSequence().takeWhile {
                    it.ptr != firstWrite.ptr
                }.none {
                    it.cmd is TACCmd.Simple.AssigningCmd && it.cmd.lhs == fpHolder
                }
            } ?: return@mapNotNull null

            // we can now instrument
            firstWrite to Instrument(
                replaceRHS = def,
                k = k,
                holder = fpHolder
            )
        }.collect(Collectors.groupingBy({ it.first.ptr }, Collectors.mapping({it.second}, Collectors.toList())))

        return c.patching {
            for((where, toAdd) in toRewrite) {
                val tempDefs = mutableListOf<TACCmd.Simple>()
                for(a in toAdd) {
                    tempDefs.add(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            lhs = a.replaceRHS.cmd.lhs,
                            rhs = TACExpr.Vec.Add(
                                a.holder.asSym(),
                                a.k.asTACSymbol().asSym()
                            ),
                            meta = a.replaceRHS.cmd.meta
                        )
                    )
                    it.replaceCommand(a.replaceRHS.ptr, listOf())
                }
                it.replace(where) { _, l ->
                    listOf(l) + tempDefs
                }
            }
        }
    }
}