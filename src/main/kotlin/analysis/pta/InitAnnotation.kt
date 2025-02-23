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

@file:kotlinx.serialization.UseSerializers(BigIntegerSerializer::class)
package analysis.pta

import analysis.CmdPointer
import analysis.alloc.AllocationAnalysis
import com.certora.collect.*
import config.Config
import log.*
import statistics.ANALYSIS_INIT_SUBKEY
import statistics.ANALYSIS_SUCCESS_STATS_KEY
import statistics.recordSuccess
import tac.MetaKey
import tac.MetaMap
import tac.NBId
import utils.*
import vc.data.*
import java.math.BigInteger
import java.util.stream.Collectors

val POP_ALLOCATION = MetaKey<AllocationAnalysis.AbstractLocation>("pta.end-allocation", erased = true)
val MARK_ZERO_WRITE = MetaKey.Nothing("pta.init.expect-zero-write")
val INIT_FAILURE = MetaKey<CmdPointer>("pta.init-alloc-failure", erased = true)
val CONSTANT_OFFSET_ALLOC_PLACEHOLDER = MetaKey.Nothing("pta.constant-offset-alloc-placeholder")

private val logger = Logger(LoggerTypes.INITIALIZATION)

object InitAnnotation {
    @KSerializable
    @Treapable
    data class ExpectBoundedWrite(
        val v: TACSymbol.Var
    ) : AmbiSerializable, TransformableVarEntityWithSupport<ExpectBoundedWrite> {
        override val support: Set<TACSymbol.Var>
            get() = setOf(v)

        override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): ExpectBoundedWrite {
            return ExpectBoundedWrite(f(v))
        }

        companion object {
            val META_KEY = MetaKey<ExpectBoundedWrite>("pta.check.bounded")
        }
    }

    @KSerializable
    data class FourByteWriteSummary(val summarized: NBId, private val skip: NBId, val fourByte: BigInteger, val base: TACSymbol.Var) : ConditionalBlockSummary {
        override val summarizedBlocks: Set<NBId>
            get() = setOf(summarized)
        override val originalBlockStart: NBId
            get() = summarized
        override val skipTarget: NBId
            get() = skip
        override val modifiedVars: Set<TACSymbol.Var>
            get() = setOf()

        override fun remapBlocks(f: (NBId) -> NBId?): FourByteWriteSummary {
            return FourByteWriteSummary(
                summarized = f(summarized)!!,
                skip = f(skip)!!,
                fourByte = fourByte,
                base = base
            )
        }

        override val variables: Set<TACSymbol.Var>
            get() = setOf()
        override val annotationDesc: String
            get() = "Write ${fourByte.toString(16)} into the beginning of $base"

        override fun toString(): String {
            return "FourByteWriteSummary: summarized $summarized; skip=$skip; fourByte=$fourByte; base=$base"
        }

        override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): TACSummary {
            return FourByteWriteSummary(
                summarized = summarized,
                skip = skip,
                fourByte = fourByte,
                base = f(base)
            )
        }
    }

    fun annotateInitializationWindows(p: CoreTACProgram) : CoreTACProgram {
        logger.info {
            "Annotating initialization windows for ${p.name}"
        }
        val g = p.analysisCache.graph
        val alloc = AllocationAnalysis.runAnalysis(g) ?: return run {
            logger.warn {
                "Allocation analysis failed for ${p.name}"
            }
            p
        }
        val cmds = try {
            SimpleInitializationAnalysis.analyze(g, alloc)
        } catch (e: Exception) {
            logger.warn(e) { "Initialization analysis failed for ${p.name}" }
            null
        } ?: run {
            recordSuccess(p.name,ANALYSIS_SUCCESS_STATS_KEY, ANALYSIS_INIT_SUBKEY,false)
            if(Config.LogInitializationStatus.get()) {
                Logger.regression {
                    "Failed initialization analysis of ${p.name}"
                }
            }
            return p.patching {
                it.addBefore(p.analysisCache.graph.roots.first().ptr, listOf(
                        TACCmd.Simple.AnnotationCmd(INIT_FAILURE, p.analysisCache.graph.roots.first().ptr)
                ))
            }
        }
        if(Config.LogInitializationStatus.get()) {
            Logger.regression {
                "Successful initialization of ${p.name}"
            }
        }
        recordSuccess(p.name,ANALYSIS_SUCCESS_STATS_KEY,ANALYSIS_INIT_SUBKEY, true)
        logger.info {
            "Done"
        }
        if(cmds.failurePoints.isNotEmpty()) {
            logger.warn {
                "Problems with the simple initialization analysis for ${p.name} at points ${cmds.failurePoints.take(10)}"
            }
        }

        /*
         * We want to make sure every byte load and store has at least one (and preferably exactly one) predecessor.
         * This gives the PTA a place to hang the pseudo allocation check for constant offset allocs.
         */
        val byteLoadStoresNoSinglePred = p.parallelLtacStream().filter {
            val preds = g.pred(it)
            ((it.cmd is TACCmd.Simple.AssigningCmd.ByteLoad && it.cmd.base == TACKeyword.MEMORY.toVar()) ||
                (it.cmd is TACCmd.Simple.AssigningCmd.ByteStore && it.cmd.base == TACKeyword.MEMORY.toVar())) &&
                    preds.size != 1
        }.collect(Collectors.toList())

        return p.toPatchingProgram().let { patch ->
            for(w in cmds.failurePoints) {
                patch.addBefore(w, listOf(TACCmd.Simple.AnnotationCmd(INIT_FAILURE, w)))
            }
            for(ltc in byteLoadStoresNoSinglePred) {
                patch.addBefore(ltc.ptr, listOf(TACCmd.Simple.AnnotationCmd(CONSTANT_OFFSET_ALLOC_PLACEHOLDER)))
            }
            for((where, aloc) in cmds.closePoints) {
                if(where in cmds.failurePoints) {
                    continue
                }
                val pops = aloc.map {
                    TACCmd.Simple.AnnotationCmd(POP_ALLOCATION, it)
                }
                patch.addBefore(where, pops)
            }
            for((e, aloc) in cmds.closeEdges) {
                val annots = aloc.map {
                    TACCmd.Simple.AnnotationCmd(POP_ALLOCATION, it)
                }
                patch.insertAlongEdge(e.first, e.second, annots)
            }
            for(loc in cmds.zeroWriteMarkers) {
                patch.addBefore(loc, listOf(TACCmd.Simple.AnnotationCmd(MARK_ZERO_WRITE)))
            }
            for ((where, write) in cmds.fourByteWrite) {
                val (summarizedBlock, succs) = patch.splitBlockRange(where, where)
                if(succs.size != 1) {
                    continue
                }
                patch.reroutePredecessorsTo(summarizedBlock,
                    listOf(
                            TACCmd.Simple.SummaryCmd(
                                    FourByteWriteSummary(
                                            base = write.base,
                                            fourByte = write.fourByte,
                                            skip = succs.first(),
                                            summarized = summarizedBlock
                                    ),
                                    meta = MetaMap()
                            )
                    )
                )
            }
            for(ptr in cmds.markTopLocs) {
                patch.replace(ptr) { c ->
                    listOf(c.plusMeta(TACMeta.NON_ALIASED_LENGTH_READ))
                }
            }
            for(ptr in cmds.markDefiniteBounds) {
                val loc = when(val accessCmd = p.analysisCache.graph.elab(ptr).cmd) {
                    is TACCmd.Simple.DirectMemoryAccessCmd -> accessCmd.loc as TACSymbol.Var
                    is TACCmd.Simple.ByteLongCopy -> accessCmd.dstOffset as TACSymbol.Var
                    else -> throw IllegalStateException("Do not understand how $accessCmd @ $ptr is an access of memory")
                }
                patch.addBefore(ptr, listOf(TACCmd.Simple.AnnotationCmd(
                    ExpectBoundedWrite.META_KEY, ExpectBoundedWrite(loc)
                )))
            }
            patch.toCode(p)
        }
    }
}
