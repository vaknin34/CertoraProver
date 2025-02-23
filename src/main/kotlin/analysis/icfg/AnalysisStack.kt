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

package analysis.icfg

import analysis.CmdPointer
import analysis.LTACCmd
import analysis.TACCommandGraph
import analysis.worklist.StatefulWorklistIteration
import analysis.worklist.StepResult
import com.certora.collect.*
import datastructures.ArrayHashMap
import datastructures.PersistentStack
import datastructures.orEmpty
import datastructures.persistentStackOf
import datastructures.stdcollections.toList
import log.*
import tac.NBId

private val logger = Logger(LoggerTypes.CALL_STACK)

/**
 * Do a stack-based analysis of the input graph
 * @param handleCmd should decide which StackAction to take based on the current command and stack, but not modify the stack by itself
 */
abstract class AnalysisStack<Record: Any>(graph: TACCommandGraph, handleCmd: (cmd: LTACCmd, stack: PersistentStack<Record>) -> StackAction<Record>) {

    private data class BlockStacks<T>(
        val stackIn: PersistentStack<T> = persistentStackOf(),
        // We only store state for commands that push/pop the stack
        val cmdState: TreapMap<CmdPointer, PersistentStack<T>> = treapMapOf()
    )

    sealed interface StackAction<T>
    protected class PopAction<T>: StackAction<T>
    protected data class PushAction<T>(val record: T): StackAction<T>
    protected class NoAction<T>: StackAction<T>

    private val blockStates = (object : StatefulWorklistIteration<NBId, Unit, Map<NBId, BlockStacks<Record>>>() {
        private val stacksIn = ArrayHashMap<NBId, PersistentStack<Record>>()
        private val stacksOut = ArrayHashMap<NBId, BlockStacks<Record>>()

        override fun submit(workItems: Iterable<NBId>): Map<NBId, BlockStacks<Record>> {
            val toSubmit = workItems.toList()
            toSubmit.forEach { root ->
                stacksIn[root] = persistentStackOf()
            }
            return super.submit(toSubmit)
        }

        override fun process(it: NBId): StepResult<NBId, Unit, Map<NBId, BlockStacks<Record>>> {
            val stackIn = stacksIn[it] ?: error("Missing input stack for block $it!")
            check(stacksOut[it] == null) { "Outgoing state of block $it already computed?" }

            var stack = stackIn
            var cmdState = treapMapOf<CmdPointer, PersistentStack<Record>>()

            for (cmd in graph.elab(it).commands) {
                when(val action: StackAction<Record> = handleCmd(cmd, stack)) {
                    is NoAction -> {}
                    is PopAction -> {
                        stack = stack.pop()
                        cmdState += (cmd.ptr to stack)
                    }
                    is PushAction<Record> -> {
                        stack = stack.push(action.record)
                        cmdState += (cmd.ptr to stack)
                    }
                }
            }

            stacksOut[it] = BlockStacks(stackIn, cmdState)

            val next = mutableListOf<NBId>()
            for (succ in graph.succ(it)) {
                val succStackIn = stacksIn[succ]
                if (succStackIn != null) {
                    if (succStackIn != stack) {
                        logger.error("Transitioning from $it to $succ, inconsistent stacks: $stack vs $succStackIn")
                    }
                } else {
                    next.add(succ)
                    stacksIn[succ] = stack
                }
            }
            return this.cont(next)
        }

        override fun reduce(results: List<Unit>): Map<NBId, BlockStacks<Record>> {
            return stacksOut
        }
    }).submit(graph.rootBlocks.map { it.id })

    protected fun stackAt(ptr: CmdPointer) = blockStates[ptr.block]?.let {
        it.cmdState.floorEntry(ptr)?.value ?: it.stackIn
    }.orEmpty()

    fun iterateUpStackPushRecords(ptr: CmdPointer): List<Record> = stackAt(ptr).toList()
    fun activationRecordsAt(ptr: CmdPointer) : Collection<Record> = stackAt(ptr).toList().reversed()
}
