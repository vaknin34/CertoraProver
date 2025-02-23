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

package rules.genericrulecheckers.helpers

import analysis.CmdPointer
import analysis.TACCommandGraph
import com.certora.collect.*
import datastructures.stdcollections.*
import tac.MetaKey
import tac.NBId
import utils.*
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACCmd.Simple.AnnotationCmd.Annotation
import java.util.concurrent.atomic.AtomicInteger

/**
 * A placeholder command manager for instrumentation.
 * Useful for instrumentations that want to change a single command pointer
 * into multiple separate instrumentation steps.
 * Using the placeholders, it is easier to replace a single command with multiple
 * multiblock changes. For example:
 * 1. Add assume commands.
 * 2. Inject a function/conditional (which will create new blocks in the resulting program)
 * 3. Add additional assumptions or calculations.
 */
class InstrumentationPlaceholderCommandsManager private constructor(
    private val ptrToPlaceHolders: MutableMap<CmdPointer, MutableList<CmdPointer>>,
    val id: Int
) {
    /**
     * Return the amount of placeholders remaining at [ptr]
     */
    fun sizeAt(ptr: CmdPointer): UInt? {
        return ptrToPlaceHolders[ptr]?.size?.toUInt()
    }

    /**
     * Remove and return the first placeholder available for [ptr]
     */
    fun popFirst(ptr: CmdPointer): CmdPointer? {
        return ptrToPlaceHolders[ptr]?.removeFirstOrNull()
    }

    /**
     * Remove and return the last placeholder available for [ptr]
     */
    fun popLast(ptr: CmdPointer): CmdPointer? {
        return ptrToPlaceHolders[ptr]?.removeLastOrNull()
    }

    /**
     * Remove and return all placeholders available for [ptr]
     */
    fun popAll(ptr: CmdPointer): List<CmdPointer>? {
        if (ptr in ptrToPlaceHolders && ptrToPlaceHolders[ptr]!!.size == 0) {
            ptrToPlaceHolders.remove(ptr)
        }
        return ptrToPlaceHolders.remove(ptr)?.toList()
    }

    private fun verifyLoc(graph: TACCommandGraph, loc: PlaceholdersLocation) {
        val phs = ptrToPlaceHolders[loc.ptr]
        check(phs != null) {"Missing placeholders for $loc"}
        phs.forEachIndexed { index, ptr ->
            val cmd = graph.elab(ptr).cmd
            check(cmd is TACCmd.Simple.AnnotationCmd && cmd.check(phKey) {
                it.managerId == id && loc == it.loc && index == it.index
            }) { "Bad instrumentation. Expecting a Annotation cmd, but found: ${graph.elab(ptr).cmd}@$ptr" }
        }
    }

    @KSerializable
    @Treapable
    sealed class PlaceholdersLocation: AmbiSerializable {
        abstract val ptr: CmdPointer
        abstract val amount: UInt

        override fun hashCode(): Int {
            return hash { it + ptr + amount }
        }

        override fun equals(other: Any?): Boolean {
            if (this === other) {
                return true
            }
            if (javaClass != other?.javaClass) {
                return false
            }
            other as Before
            return ptr == other.ptr && amount == other.amount
        }

        @KSerializable
        @Treapable
        class Before(override val ptr: CmdPointer, override val amount: UInt) : PlaceholdersLocation()
        @KSerializable
        @Treapable
        class After(override val ptr: CmdPointer, override val amount: UInt) : PlaceholdersLocation()
        @KSerializable
        @Treapable
        class Replace(override val ptr: CmdPointer, override val amount: UInt) : PlaceholdersLocation()
    }

    companion object {
        private val phManagerCounter = AtomicInteger(0)

        @KSerializable
        @Treapable
        data class PlaceholderData(val index: Int, val loc: PlaceholdersLocation, val managerId: Int)
            : AmbiSerializable

        /**
         * Metakey representing this annotation is for a placeholder described in PlaceholderData.
         */
        private const val phKeyName = "PlaceholderData"
        val phKey = MetaKey<PlaceholderData>(phKeyName)

        /**
         * @return @param[amount] command pointers following @param[ptr] (inclusive)
         * Result pointers must be in the same block
         */
        private fun collectPtrsFrom(graph: TACCommandGraph, ptr: CmdPointer, amount: Int): List<CmdPointer> {
            val block = graph.elab(ptr.block)
            check(block.commands.size >= ptr.pos + amount) { "Bad instrumentation. Was Expecting " +
                "${ptr.pos + amount} straight line commands after $ptr, but found ${block.commands.size}" }
            return block.commands.subList(ptr.pos, ptr.pos + amount).map { it.ptr }
        }

        /**
         * @return @param[amount] command pointers following @param[ptr] (exclusive)
         * Result pointers must be in the same block
         */
        private fun collectNextPtrs(graph: TACCommandGraph, ptr: CmdPointer, amount: Int): List<CmdPointer> {
            return collectPtrsFrom(graph, ptr, amount + 1).drop(1)
        }

        /**
         * @return @param[amount] command pointers preceding @param[ptr]
         * Result pointers must be in the same block
         */
        private fun collectPrevPtrs(graph: TACCommandGraph, ptr: CmdPointer, amount: Int): List<CmdPointer> {
            val block = graph.elab(ptr.block)
            check(ptr.pos >= amount) { "Bad instrumentation. Was Expecting $amount straight line commands " +
                "before $ptr, but found ${ptr.pos}" }
            return block.commands.subList(ptr.pos - amount, ptr.pos).map { it.ptr }
        }

        /**
         * Patches the given [prog] at each cmdPointer in [locs].
         * For each (cmdPointer, amount) in [locs] the resulting [InstrumentationPlaceholderCommandsManager] will contain amount placeholders.
         */
        fun createPlaceholders(prog: CoreTACProgram, locs: List<PlaceholdersLocation>)
            : Pair<CoreTACProgram, InstrumentationPlaceholderCommandsManager> {
            require(locs.mapToSet { it.ptr }.size == locs.size) { "Cannot create placeholders for the same cmd more than once" }

            val ptrToPlaceHolders = mutableMapOf<CmdPointer, MutableList<CmdPointer>>()
            val id = phManagerCounter.incrementAndGet()
            // Add placeholders commands and create a new CoreTACProgram
            val newProg = with(prog.toPatchingProgram()) {
                for (loc in locs) {
                    val commands = (0 until loc.amount.toInt()).map {
                        TACCmd.Simple.AnnotationCmd(Annotation(phKey, PlaceholderData(it, loc, id)))
                    }
                    when (loc) {
                        is PlaceholdersLocation.After ->
                            insertAfter(loc.ptr, commands)

                        is PlaceholdersLocation.Before ->
                            addBefore(loc.ptr, commands)

                        is PlaceholdersLocation.Replace ->
                            replaceCommand(loc.ptr, commands)
                    }
                }
                toCode(prog)
            }

            // Calculate the locations of the created placeholder commands
            val graph = newProg.analysisCache.graph
            val updatedBlocks = mutableMapOf<NBId, Int>()
            val sorted = locs.sortedBy { it.ptr }
            for (loc in sorted) {
                val curBlock = loc.ptr.block
                updatedBlocks[curBlock] = updatedBlocks[curBlock] ?: 0
                val fixedStartPtr = CmdPointer(loc.ptr.block, loc.ptr.pos + updatedBlocks[curBlock]!!)
                updatedBlocks[curBlock] = updatedBlocks[curBlock]!! + loc.amount.toInt()

                ptrToPlaceHolders[loc.ptr] = when (loc) {
                    is PlaceholdersLocation.After -> {
                        collectNextPtrs(graph, fixedStartPtr, loc.amount.toInt())
                    }
                    is PlaceholdersLocation.Before -> {
                        // When taking ptr after adding placeholder before we need to look further ahead
                        val fixedForBefore = CmdPointer(loc.ptr.block, loc.ptr.pos + updatedBlocks[curBlock]!!)
                        collectPrevPtrs(graph, fixedForBefore, loc.amount.toInt())
                    }
                    is PlaceholdersLocation.Replace -> {
                        updatedBlocks[curBlock] = updatedBlocks[curBlock]!! - 1
                        collectPtrsFrom(graph, fixedStartPtr, loc.amount.toInt())
                    }
                }.toMutableList()
            }

            val manager = InstrumentationPlaceholderCommandsManager(ptrToPlaceHolders, id)
            check(ptrToPlaceHolders.keys.intersect(locs.map { it.ptr }).size == ptrToPlaceHolders.size) {
                "Placeholder in unexpected pointer"}
            locs.forEach { loc ->
                manager.verifyLoc(graph, loc)
            }
            return newProg to manager
        }
    }
}
