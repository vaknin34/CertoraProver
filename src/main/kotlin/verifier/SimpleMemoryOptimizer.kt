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

package verifier

import analysis.CmdPointer
import analysis.CommandWithRequiredDecls
import analysis.dataflow.LiveVariableAnalysis
import analysis.icfg.ExpressionSimplifier
import analysis.maybeNarrow
import analysis.pta.LoopCopyAnalysis
import config.Config
import optimizer.OptimizeBasedOnPointsToAnalysis
import tac.NBId
import tac.Tag
import utils.*
import vc.data.*
import vc.data.SimplePatchingProgram.Companion.patchForEach
import vc.data.tacexprutil.getFreeVars
import java.math.BigInteger
import java.util.stream.Collectors
import java.util.stream.Stream
import datastructures.stdcollections.*

object SimpleMemoryOptimizer {
    /**
     * credit: jtoman
     * removing unused memory stores
     */
    fun removeUnusedWrites(c: CoreTACProgram) : CoreTACProgram {
        val commandDroppingLVA = LiveVariableAnalysis(c.analysisCache.graph) { it.cmd !is TACCmd.Simple.LogCmd && it.cmd !is TACCmd.Simple.SummaryCmd && it.cmd !is TACCmd.Simple.AnnotationCmd }
        val toRemoveWrites = c.parallelLtacStream().mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd.ByteStore>()
        }.filter {
            !commandDroppingLVA.isLiveAfter(it.ptr, it.cmd.base)
        }.map {
            it.ptr to it.cmd.base
        }.collect(Collectors.groupingBy({it.second}, Collectors.mapping({it.first}, Collectors.toSet())))
        return c.patching {
            for((_, loc) in toRemoveWrites) {
                if(loc.size != 1) {
                    continue
                }
                it.replaceCommand(loc.single(), listOf(TACCmd.Simple.NopCmd))
            }
        }
    }

    fun rewriteCopyLoops(c: CoreTACProgram) : CoreTACProgram {
        if(!Config.EnabledCopyLoopRewrites.get()) {
            return c
        }
        return c.parallelLtacStream().mapNotNull {
            it.maybeNarrow<TACCmd.Simple.SummaryCmd>()?.takeIf {
                it.cmd.summ is LoopCopyAnalysis.LoopCopySummary
            }
        }.filter {
            val summ = it.cmd.summ as LoopCopyAnalysis.LoopCopySummary
            OptimizeBasedOnPointsToAnalysis.SUMMARY_VALIDATED in it.cmd.meta && summ.assumedSize == BigInteger.ONE &&
                summ.valueSummary.all { (k, v) ->
                    !c.analysisCache.lva.isLiveBefore(summ.skipTarget, k) ||
                        v is LoopCopyAnalysis.LoopValueSummary.Identity ||
                        (v is LoopCopyAnalysis.LoopValueSummary.WeaklyIncreasing && v.definition != null && v.mustWrite)
                }
        }.patchForEach(c) {
            val summ = it.cmd.summ as LoopCopyAnalysis.LoopCopySummary
            this.consolidateEdges(summ.skipTarget, listOf(summ.originalBlockStart), object : PatchingTACProgram.CommandRemapper<TACCmd.Simple> {
                override fun isJumpCommand(c: TACCmd.Simple): Boolean {
                    return PatchingTACProgram.SIMPLE.isJumpCommand(c)
                }

                override fun remapSuccessors(c: TACCmd.Simple, remapper: (NBId) -> NBId): TACCmd.Simple {
                    check(c is TACCmd.Simple.SummaryCmd)
                    return TACCmd.Simple.JumpCmd(summ.skipTarget)
                }
            })
            val valueSummaries = summ.valueSummary.filter { (k, v) ->
                v is LoopCopyAnalysis.LoopValueSummary.WeaklyIncreasing && c.analysisCache.lva.isLiveBefore(summ.skipTarget, k)
            }.map { (k, v) ->
                check(v is LoopCopyAnalysis.LoopValueSummary.WeaklyIncreasing && v.definition != null) {
                    "invariant broken, any live weakly increasing summaries must have a definition for this rewrite"
                }
                this.addVarDecls(v.definition.getFreeVars())
                this.addVarDecl(k)
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = k,
                    rhs = v.definition
                )
            }
            this.insertAlongEdge(it.ptr.block, summ.skipTarget, valueSummaries + listOf(
                TACCmd.Simple.ByteLongCopy(
                    srcBase = summ.sourceMap,
                    dstBase = summ.destMap,
                    length = summ.lenVars.first(),
                    srcOffset = summ.inPtr.first(),
                    dstOffset = summ.outPtr.first()
                )
            ))
        }
    }

    fun removeDeadPartitions(c: CoreTACProgram) : CoreTACProgram {
        if(!Config.EnabledAggressivePartitionPruning.get()) {
            return c
        }
        val livePartitions = c.parallelLtacStream().filter {
            it.cmd !is TACCmd.Simple.AssigningCmd.ByteStore && it.cmd !is TACCmd.Simple.LogCmd && it.cmd !is TACCmd.Simple.SummaryCmd && it.cmd !is TACCmd.Simple.AnnotationCmd
        }.flatMap {
            if(it.cmd is TACCmd.Simple.ByteLongCopy) {
                Stream.of(it.cmd.srcBase)
            } else {
                it.cmd.getFreeVarsOfRhs().filter {
                    it.tag == Tag.ByteMap
                }.stream()
            }
        }.collect(Collectors.toSet())
        return c.parallelLtacStream().filter {
            (it.cmd is TACCmd.Simple.AssigningCmd.ByteStore && it.cmd.base !in livePartitions) ||
                (it.cmd is TACCmd.Simple.ByteLongCopy && it.cmd.dstBase !in livePartitions)
        }.patchForEach(c) {
            this.replaceCommand(it.ptr, listOf(TACCmd.Simple.NopCmd))
        }
    }

    /**
     * Converts the [TACCmd.Simple.ByteLongCopy] command [c] @ [where] that is assumed to copy the string [str] to a sequence of
     * word-sized (32 bytes) chunk stores to the memory.
     * E.g. [str] of length 32*N+K for k<32 is partitioned to N+1 chunks, and writes:
     * c.dstBase[c.dstOffset+0]=chunk[0]
     * ...
     * c.dstBase[c.dstOffset+32*N]=chunk[N]
     * c.dstBase[c.dstOffset+32*(N+1)]=chunk[N+1]||0..0 (padding)
     *
     * credit: shelly
     */
    fun rewriteByteLongCopyThatCopiesString(
        str: String,
        c: TACCmd.Simple.ByteLongCopy,
        where: CmdPointer,
        expSimplifier: ExpressionSimplifier
    ): CommandWithRequiredDecls<TACCmd.Simple> {
        val dstOffsetTmp = TACKeyword.TMP(Tag.Bit256)
        val cmds = mutableListOf<TACCmd.Simple>()
        val syms = mutableSetOf<TACSymbol.Var>()

        (0..(str.length / 32)).forEach { chunkIdx ->
            val chunk = str.substring(chunkIdx * 32, Math.min(str.length, chunkIdx * 32 + 32))
            val chunkPadding = (0..((32 - chunk.length) - 1)).map { 0.toByte() }
            @Suppress("DEPRECATION") val wholeChunk = chunk.map { c -> c.toByte() } + chunkPadding
            check(wholeChunk.size == 32)
            {
                "Chunk size should be 32 but got whole $wholeChunk (${wholeChunk.size}) consisting of " +
                        "chunk $chunk (${chunk.length}) + padding $chunkPadding (${chunkPadding.size})"
            }
            val chunkAsValue = wholeChunk.map { b -> b.toHexString() }.joinToString("").let { s ->
                check(s.length == 64)
                { "String $s (${s.length}) of whole chunk $wholeChunk is not a 32-byte (64 in hex representation) long string" }
                s.toBigInteger(16)
            }

            fun assignToDstOffset(dstOffset: TACSymbol, value: TACSymbol, dstBase: TACSymbol.Var): Pair<TACCmd.Simple,Set<TACSymbol.Var>> {
                // special case for special tac locations
                return if (dstOffset == TACSymbol.Companion.lift(0)) {
                    val mem0 = TACKeyword.MEM0.toVar()
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        mem0,
                        value,
                    ) to setOf(mem0)
                } else if (dstOffset == TACSymbol.Companion.lift(32)) {
                    val mem32 = TACKeyword.MEM32.toVar()
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        mem32,
                        value,
                    ) to setOf(mem32)
                } else if (dstOffset == TACSymbol.Companion.lift(64)) {
                    // this is so illegal but meh
                    val mem64 = TACKeyword.MEM64.toVar()
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        mem64,
                        value,
                    ) to setOf(mem64)
                } else {
                    TACCmd.Simple.AssigningCmd.ByteStore(
                        dstOffset,
                        value,
                        dstBase
                    ) to emptySet()
                }
            }


            val dst = expSimplifier.simplify(c.dstOffset, where, true).getAsConst()

            // dstOffsetTmp = c.dstOffset+chunkIdx*32
            // c.dstBase[dstOffsetTmp] = chunk[chunkIdx]
            if (dst != null) {
                assignToDstOffset(
                    (dst + chunkIdx.toBigInteger() * 32.toBigInteger()).asTACSymbol(),
                    TACSymbol.Const(chunkAsValue),
                    c.dstBase
                ).let { (_cmds, _syms) ->
                    cmds.add(_cmds)
                    syms.addAll(_syms)
                }
            } else {
                val calcOffset =
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        dstOffsetTmp,
                        c.dstOffset,
                        TACSymbol.Const((chunkIdx * 32).toBigInteger()),
                        TACExprFactUntyped::Add
                    )
                val storeChunk =
                    TACCmd.Simple.AssigningCmd.ByteStore(
                        dstOffsetTmp,
                        TACSymbol.Const(chunkAsValue),
                        c.dstBase
                    )

                cmds.addAll(listOf(calcOffset, storeChunk))
                syms.add(dstOffsetTmp)
            }
        }
        return CommandWithRequiredDecls(
            cmds,
            syms
        )
    }

}
