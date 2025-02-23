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

import com.certora.collect.*
import datastructures.stdcollections.*
import utils.*

interface BlockCommandView<Block, Cmd, CmdPtr> {
    fun commands(b: Block): List<Cmd>
    fun ptr(c: Cmd): CmdPtr
}

abstract class CommandDataflowAnalysis<Graph, Block, @Treapable BlockLabel, Cmd, CmdPtr, T: Any>(
    graph: Graph,
    lattice: JoinLattice<T>,
    initial: T,
    dir: Direction,
    graphView: GraphBlockView<Graph, Block, BlockLabel>,
    private val cmdView: BlockCommandView<Block, Cmd, CmdPtr>
) : BlockDataflowAnalysis<Graph, Block, BlockLabel, T>(graph, lattice, initial, dir, graphView) {

    private val _cmdIn = mutableMapOf<CmdPtr, T>()
    private val _cmdOut = mutableMapOf<CmdPtr, T>()

    protected abstract inner class Finalizer : BlockDataflowAnalysis<Graph, Block, BlockLabel, T>.Finalizer() {
        override fun finalizeBlock(block: Block) {
            cmdView.commands(block).forEach {
                val ptr = cmdView.ptr(it)
                _cmdIn[ptr] = finalizeState(_cmdIn[ptr]!!)
                _cmdOut[ptr] = finalizeState(_cmdOut[ptr]!!)
            }
        }
    }

    override fun transform(inState: T, block: Block): T {
        val cmds = if(direction === Direction.BACKWARD) {
            cmdView.commands(block).reversed()
        } else {
            cmdView.commands(block)
        }
        var state = inState
        cmds.forEach {
            _cmdIn[cmdView.ptr(it)] = state
            val newState = transformCmd(state, it)
            _cmdOut[cmdView.ptr(it)] = newState
            state = newState
        }
        return state
    }

    val cmdIn : Map<CmdPtr, T>
        get() = _cmdIn

    val cmdOut : Map<CmdPtr, T>
        get() = _cmdOut

    abstract fun transformCmd(inState: T, cmd: Cmd) : T
}

