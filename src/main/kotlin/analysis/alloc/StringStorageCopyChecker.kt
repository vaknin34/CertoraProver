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

package analysis.alloc

import analysis.CmdPointer
import analysis.TACCommandGraph
import analysis.alloc.StringStorageCopyChecker.AllocationWorker
import analysis.alloc.StringStorageCopyChecker.isDecodeAllocation
import analysis.maybeNarrow
import analysis.smtblaster.BitBlaster
import analysis.smtblaster.IBlaster
import analysis.smtblaster.Z3BlasterPool
import analysis.snarrowOrNull
import datastructures.stdcollections.*
import evm.MAX_EVM_UINT256
import instrumentation.StoragePackedLengthSummarizer
import parallel.ParallelPool
import parallel.ParallelPool.Companion.runInherit
import parallel.Scheduler
import parallel.forkEvery
import parallel.pcompute
import tac.NBId
import utils.firstMapped
import vc.data.*

/**
 * Find those allocations (updates of the free pointer) which correspond to a copy of a string from storage
 * to memory. These allocations look like a regular array allocation, but the initialization code is a nightmare,
 * and must be handled specially. The main worker here finds decodes of the string length from storage (as discovered
 * by the [StoragePackedLengthSummarizer]) and seeing if this length is used in a special allocation pattern, where
 * the free pointer is bumped by the length rounded up to the nearest multiple of 32 plus 32. The actual checking
 * of this pattern for a specific length read is is implemented in [isDecodeAllocation], the [AllocationWorker] finds all
 * such allocations.
 */
object StringStorageCopyChecker {
    private const val synthFreePointer = "certora!freePointer"
    private const val synthLength = "certora!lenField"

    /**
     * Given a smt blaster [blaster], a [block] in graph [g] and the length of a storage string array in [decodedLen],
     * is the free pointer updated to hold an array of the string length.
     *
     * Put another way, if we enter [block] having just decoded a storage string's length into [decodedLen], do we immediately
     * see an update of the free pointer to hold a string (in memory) of that length. If so, the [CmdPointer] of the free
     * pointer update is returned, otherwise we return null.
     */
    fun isDecodeAllocation(block: NBId, decodedLen: TACSymbol.Var, g: TACCommandGraph, blaster: IBlaster) : CmdPointer? {
        val tacBlock = g.elab(block)
        /*
          Find the (unique) FP update in the successor block
         */
        val fpUpdate = tacBlock.commands.firstOrNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd>()?.cmd?.lhs == TACKeyword.MEM64.toVar()
        } ?: return null
        val newFp = (fpUpdate.cmd as? TACCmd.Simple.AssigningCmd.AssignExpCmd)?.rhs?.let { it as? TACExpr.Sym.Var }?.s ?: return null
        /*
          Find the preceding read locations, and associate them with the "freePointer" synthetic id
         */
        val readLocs = g.iterateUntil(fpUpdate.ptr).mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.takeIf {
                it.cmd.rhs.equivSym(TACKeyword.MEM64)
            }?.ptr
        }.associateWith {
            synthFreePointer
        }
        /*
          Is the new value of the free pointer defined by synthFreePointer + 32 + roundUpTo32(decodedLen)?
         */
        if(!BitBlaster.blastCode(
                block = tacBlock,
                synthAssign = readLocs,
                start = 0,
                end = fpUpdate.ptr.pos,
                env = mapOf(decodedLen to synthLength),
                blaster = blaster,
                vcGen = vc@{
                    val upperMask = MAX_EVM_UINT256.andNot(31.toBigInteger())
                    val fpIdent = it[newFp] ?: return@vc false
                    assert {
                        lnot(
                            eq(
                                toIdent(fpIdent),
                                plus(
                                    toIdent(synthFreePointer), const(32), bwAnd(
                                        const(upperMask),
                                        plus(
                                            const(31), toIdent(synthLength)
                                        )
                                    )!!
                                )
                            )
                        )
                    }
                    true
                }
            )) {
            return null
        }
        /*
          Check that we write decodedLen into the length field of the newly allocated block.

          Do this by iterating from the update pointer, and so long as there are no intervening assignments
          to decoded len, find the first write.
         */
        val lenWrite = g.iterateBlock(fpUpdate.ptr).takeWhile {
            it.cmd !is TACCmd.Simple.AssigningCmd || it.cmd.lhs != decodedLen
        }.firstMapped {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd.ByteStore>()?.takeIf {
                it.cmd.base == TACKeyword.MEMORY.toVar()
            }
        } ?: return null
        val writeCmd = lenWrite.cmd
        if(writeCmd.value !is TACSymbol.Var || writeCmd.loc !is TACSymbol.Var) {
            return null
        }
        /*
          This proves that writeCmd.loc@lenWrite.ptr is equal to the block we want because, in program order:
          readLocs <= fpWrite <= lenWrite, and thus this is straightline code with no intervening assignments. So
          the value couldn't possibly change.
         */
        if (g.cache.def.defSitesOf(writeCmd.loc, lenWrite.ptr).singleOrNull()?.let {
                it in readLocs
            } == false || writeCmd.value != decodedLen) {
            return null
        }
        return fpUpdate.ptr
    }

    private class AllocationWorker(private val g: TACCommandGraph) {
        /**
         * Find all storage string allocations, this just scans the successor blocks of all
         * [instrumentation.StoragePackedLengthSummarizer.StorageLengthReadSummary] and checks whether it contains
         * the appropriate free pointer update, as determined by [isDecodeAllocation]
         */
        fun compute(): Map<CmdPointer, AllocationAnalysis.Alloc.StorageUnpack> {
            val toRet = mutableMapOf<CmdPointer, AllocationAnalysis.Alloc.StorageUnpack>()
            val cand = g.blocks.mapNotNull {
                it.commands.last().snarrowOrNull<StoragePackedLengthSummarizer.StorageLengthReadSummary>()?.let {
                    Triple(it.skipTarget, it.outputVar, it.readSort)
                }
            }.forkEvery { (block, decodedLen, sort) ->
                Scheduler.fork {
                    ParallelPool.allocInScope({ _ -> Z3BlasterPool() }) { blaster ->
                        isDecodeAllocation(block, decodedLen, g, blaster)?.let { fpUpdate ->
                            Triple(block, fpUpdate, sort)
                        }.let(Scheduler::complete)
                    }
                }
            }.pcompute().runInherit().filterNotNull()
            for((block, update, sort) in cand) {
                toRet[update] = AllocationAnalysis.Alloc.StorageUnpack(
                    slotRead = g.elab(block).commands.first().ptr to sort
                )
            }

            return toRet
        }
    }

    fun analyzeStringAllocations(g: TACCommandGraph) = AllocationWorker(g).compute()
}
