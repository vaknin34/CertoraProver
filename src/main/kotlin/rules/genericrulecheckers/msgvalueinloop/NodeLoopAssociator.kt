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

package rules.genericrulecheckers.msgvalueinloop

import analysis.*
import config.Config
import datastructures.stdcollections.*
import decompiler.BMCRunner.Companion.unwindingCondMsg
import log.Logger
import log.LoggerTypes
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACMeta
import vc.data.TACMeta.SCOPE_SNIPPET_END

private val logger = Logger(LoggerTypes.GENERIC_RULE)

val joinLattice = JoinLattice.ofJoin<List<CmdPointer>> { b1, b2 ->
    check(b1.size == b2.size) {"Expecting all block predecessors to have the same amount of open loops at each" +
        " point of the program. b1 = $b1 b2 = $b2"}
    b1
}

/**
 * Returns the set of nodes (CmdPointer) that are inside loops.
 * Forward dataflow analysis for the formula:
 *   state = openloops (bottom is empty)
 *   3 command types:
 *      openloop -> state = state ∪ cmdPtr
 *      closeloop -> state = state / state.last()
 *      other -> state = state
 *   Join -> state = state1 (assert state1.size == state2.size)
 *  The analysis should be monotonic because join would never change the state.
 */
class NodeLoopAssociator(val tacProgram: CoreTACProgram):
    TACCommandDataflowAnalysis<List<CmdPointer>>(tacProgram.analysisCache.graph, joinLattice, listOf(), Direction.FORWARD) {
    init {
        runAnalysis()
        check( Config.IsAssumeUnwindCondForLoops.get() || graph.sinkBlocks.all {
            // all sink blocks are either not in a loop, or end with an assert-unwind cond
            (cmdOut.get(it.commands.last().ptr)?.isEmpty()
                ?: throw IllegalStateException("no result for ${it.commands.last().ptr} in NodeLoopAssociator"))
                /* see unwindCondCheck in BMC to understand this pattern */
                || (it.commands.last().maybeAnnotation(SCOPE_SNIPPET_END)
                        && it.commands.dropLast(1).lastOrNull()?.let { oneBeforeLast ->
                            oneBeforeLast.cmd is TACCmd.Simple.AssertCmd && oneBeforeLast.cmd.description == unwindingCondMsg()
                        } == true)
        }) {
            "Should always end program ${tacProgram.name} outside of loop, but found ${
                graph.sinkBlocks.filter {
                    cmdOut.get(it.commands.last().ptr)?.isNotEmpty() == true
                }.map { it.id }
            }"
        }
    }

    fun computeCmdPtrs(): Set<CmdPointer> =
        this.cmdOut.filter { it.value.isNotEmpty() }.keys

    private fun isEndLoop(cmdPointer: CmdPointer): Boolean =
        graph.elab(cmdPointer).maybeAnnotation(TACMeta.END_LOOP)

    private fun isStartLoop(cmdPointer: CmdPointer): Boolean =
        graph.elab(cmdPointer).maybeAnnotation(TACMeta.START_LOOP) != null

    override fun transformCmd(inState: List<CmdPointer>, cmd: LTACCmd): List<CmdPointer> {
        return if (isEndLoop(cmd.ptr)) {
            logger.trace { "Loop end@${cmd.ptr}" }
            check(inState.isNotEmpty()) {"Received end loop when there is no open loop in " +
                    "${tacProgram.name}@${cmd.ptr} cmd is ${tacProgram.analysisCache.graph.elab(cmd.ptr)}"}
            inState.dropLast(1)
        } else if (isStartLoop(cmd.ptr)) {
            logger.trace { "Loop start@${cmd.ptr}" }
            inState.plus(cmd.ptr)
        } else {
            inState
        }
    }
}
