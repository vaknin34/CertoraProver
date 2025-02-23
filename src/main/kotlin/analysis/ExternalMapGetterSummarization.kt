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

package analysis

import analysis.smtblaster.*
import parallel.ParallelPool
import tac.MetaMap
import tac.NBId
import utils.*
import vc.data.*
import java.util.stream.Collectors

object ExternalMapGetterSummarization {
    private data class ToRewrite(
        val start: CmdPointer,
        val end: CmdPointer,
        val slot: TACSymbol,
        val hashOutput: TACSymbol.Var,
        val baseArray: TACSymbol.Var
    )

    @KSerializable
    data class ExternalGetterHash(
        val output: TACSymbol.Var,
        val keyArray: TACSymbol.Var,
        val slot: TACSymbol,
        override val originalBlockStart: NBId,
        override val skipTarget: NBId
    ) : ConditionalBlockSummary, AmbiSerializable {
        override val summarizedBlocks: Set<NBId>
            get() = setOf(originalBlockStart)

        override val modifiedVars: Set<TACSymbol.Var>
            get() = setOf(output)

        override fun remapBlocks(f: (NBId) -> NBId?): ConditionalBlockSummary {
            return ExternalGetterHash(
                output = output,
                keyArray = keyArray,
                slot = slot,
                originalBlockStart = f(originalBlockStart)!!,
                skipTarget = f(skipTarget)!!
            )
        }

        override val variables: Set<TACSymbol.Var>
            get() = setOfNotNull(output, slot as? TACSymbol.Var)
        override val annotationDesc: String
            get() = "Unsafe hash slot $slot into $output"

        override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): TACSummary {
            return ExternalGetterHash(
                output = f(output),
                keyArray = f(keyArray),
                slot = (slot as? TACSymbol.Var)?.let(f) ?: slot,
                originalBlockStart = originalBlockStart,
                skipTarget = skipTarget
            )
        }

    }

    fun annotate(c: CoreTACProgram): CoreTACProgram {
        val graph = c.analysisCache.graph
        val toRewrite = ParallelPool.allocInScope({
            Z3BlasterPool()
        }) { pool ->
            c.parallelLtacStream().mapNotNull {
                it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignSha3Cmd>()
            }.mapNotNull {
                var numLoads = 0
                /*
                  Take the shortest prefix of commands before the hash command that includes two byteloads. If
                  such a straightline prefix does not exist, the takeUntil returns null.
                 */
                graph.iterateUntil(it.ptr).reversed().takeUntil {
                    if(it.cmd !is TACCmd.Simple.AssigningCmd.ByteLoad) {
                        false
                    } else {
                        ++numLoads == 2
                    }
                    /* the prefix has been reversed, so reverse it here, so we have the prefix now in program order*/
                }?.reversed()
                        /* append the hash command */
                    ?.plus(it.wrapped)?.takeIf {
                        /* accept only our byte loads, jump dests, stores, hashes, jumpdests, and expression assignments */
                    it.all {
                        (it.cmd is TACCmd.Simple.AssigningCmd.ByteStore && it.cmd.base == TACKeyword.MEMORY.toVar()) ||
                                (it.cmd is TACCmd.Simple.AssigningCmd.ByteLoad && it.cmd.base == TACKeyword.MEMORY.toVar()) ||
                                it.cmd is TACCmd.Simple.AssigningCmd.AssignSha3Cmd ||
                                it.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd ||
                                it.cmd is TACCmd.Simple.JumpdestCmd
                    }
                }
            }.mapNotNull {
                val lst = it.last()
                val succ = graph.succ(lst).singleOrNull()?.takeIf {
                    it.cmd is TACCmd.Simple.AssigningCmd.ByteStore && it.cmd.base == TACKeyword.MEMORY.toVar()
                } ?: return@mapNotNull null
                it + succ
            }.mapNotNull { seq ->
                /* we expect to see two reads, in order:
                   1. The length, and
                   2. The old value

                   And we expect to see two writes, in order:
                   1. the slot, and
                   2. the saved old value

                   by the previous map not null block, we must have that the second write comes *after* the hash

                   seq is in PO, so loads and stores are also in program order. Further, we know that seq must have
                   exactly one assign hash, and it must be the penultimate element. Thus, all reads and the first write
                   must come before the hash
                 */
                val (loads, stores) = seq.mapNotNull {
                    it.takeIf { it.cmd is TACCmd.Simple.DirectMemoryAccessCmd }
                }.takeIf {
                    it.all {
                        (it.cmd as TACCmd.Simple.DirectMemoryAccessCmd).loc is TACSymbol.Var
                    }
                }?.partition {
                    it.cmd is TACCmd.Simple.AssigningCmd.ByteLoad
                } ?: return@mapNotNull null
                if (loads.size != 2 && stores.size != 2) {
                    return@mapNotNull null
                }
                if (loads.any {
                        it.ptr.pos > stores.first().ptr.pos
                    }) {
                    return@mapNotNull null
                }
                val hashLoc = seq.firstMapped {
                    it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignSha3Cmd>()
                }!!
                val liveAfter = graph.cache.lva.liveVariablesAfter(seq.last().ptr)
                for(s in seq) {
                    if(s.cmd is TACCmd.Simple.AssigningCmd && s.cmd !is TACCmd.Simple.DirectMemoryAccessCmd && s.ptr != hashLoc.ptr && s.cmd.lhs in liveAfter) {
                        return@mapNotNull null
                    }
                }
                val script = SmtExpScriptBuilder(
                    termBuilder = SmtExpIntTermBuilder
                )
                val blaster = SmtExpIntBlaster()
                script.declare("BASE")
                script.declare("LEN")
                script.declareFun("read", 1)


                val declared = mutableSetOf<TACSymbol.Var>()
                val basePointer = (loads.first().cmd as TACCmd.Simple.DirectMemoryAccessCmd).loc as TACSymbol.Var
                for (s in seq) {
                    if (s.cmd !is TACCmd.Simple.AssigningCmd) {
                        continue
                    }
                    if (s.cmd.lhs in declared) {
                        return@mapNotNull null
                    }
                    if (s.cmd is TACCmd.Simple.AssigningCmd.ByteLoad) {
                        if (s.cmd.loc == basePointer) {
                            script.define(s.cmd.lhs.smtRep) {
                                toIdent("LEN")
                            }
                        } else if (s.cmd.loc !is TACSymbol.Var || s.cmd.loc !in declared) {
                            return@mapNotNull null
                        } else {
                            script.define(s.cmd.lhs.smtRep) {
                                apply("read", listOf(toIdent(s.cmd.loc.smtRep)))
                            }
                        }
                    } else if (s.cmd is TACCmd.Simple.AssigningCmd.ByteStore) {
                        check(s in stores)
                        if (s.cmd.loc !in declared) {
                            return@mapNotNull null
                        }
                        if (s.ptr == stores[1].ptr && s.cmd.value !in declared) {
                            return@mapNotNull null
                        }
                        continue
                    } else if (s.cmd is TACCmd.Simple.AssigningCmd.AssignSha3Cmd) {
                        if (s.cmd.op1 !in declared || s.cmd.op2 !in declared) {
                            return@mapNotNull null
                        }
                        continue
                    } else if (s.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
                        val e = blaster.blastExpr(s.cmd.rhs) {
                            if (it == basePointer) {
                                "BASE"
                            } else {
                                it.smtRep
                            }
                        } ?: return@mapNotNull null
                        script.define(s.cmd.lhs.smtRep) {
                            e
                        }
                    } else {
                        `impossible!`
                    }
                    declared.add(s.cmd.lhs)
                }
                val hashBase = (hashLoc.cmd.op1 as TACSymbol.Var).smtRep
                val hashLength = (hashLoc.cmd.op2 as TACSymbol.Var).smtRep
                fun <T> ISMTTermBuilder<*, T>.toIdent(v: TACSymbol.Var) = toIdent(v.smtRep)
                script.assert {
                    lnot(
                        land(
                            eq(
                                plus(
                                    toIdent("LEN"), const(32)
                                ),
                                toIdent(hashLength)
                            ),
                            eq(
                                toIdent(hashBase),
                                plus(
                                    toIdent("BASE"), const(32)
                                )
                            ),
                            eq(
                                toIdent(stores[0].narrow<TACCmd.Simple.AssigningCmd.ByteStore>().cmd.loc as TACSymbol.Var),
                                plus(
                                    toIdent("BASE"), const(32), toIdent("LEN")
                                )
                            ),
                            eq(
                                toIdent(stores[1].narrow<TACCmd.Simple.AssigningCmd.ByteStore>().cmd.loc as TACSymbol.Var),
                                plus(
                                    toIdent("BASE"), const(32), toIdent("LEN")
                                )
                            ),
                            eq(
                                toIdent(stores[1].narrow<TACCmd.Simple.AssigningCmd.ByteStore>().cmd.value as TACSymbol.Var),
                                apply(
                                    "read",
                                    listOf(
                                        plus(toIdent("BASE"), const(32), toIdent("LEN"))
                                    )
                                )
                            )
                        )
                    )
                }
                if(!pool.blastSmt(script.cmdList)) {
                    return@mapNotNull null
                }
                ToRewrite(
                    start = seq.first().ptr,
                    end = seq.last().ptr,
                    slot = stores[0].narrow<TACCmd.Simple.AssigningCmd.ByteStore>().cmd.value,
                    hashOutput = hashLoc.cmd.lhs,
                    baseArray = basePointer
                )
            }.collect(Collectors.toList())
        }
        if(toRewrite.isEmpty()) {
            return c
        }
        return c.patching { p ->
            toRewrite.forEach {
                val (blk, succ) = p.splitBlockRange(it.start, it.end)
                val soleSucc = succ.singleOrNull() ?: return@forEach
                val summary = ExternalGetterHash(
                    originalBlockStart = blk,
                    skipTarget = soleSucc,
                    slot = it.slot,
                    output = it.hashOutput,
                    keyArray = it.baseArray
                )
                p.reroutePredecessorsTo(blk, listOf(
                    TACCmd.Simple.SummaryCmd(
                        summary,
                        MetaMap()
                    )
                ), summary.successors)
            }
        }
    }
}
