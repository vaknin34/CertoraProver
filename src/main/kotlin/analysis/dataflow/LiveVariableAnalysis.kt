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

package analysis.dataflow

import analysis.*
import com.certora.collect.*
import datastructures.stdcollections.*
import tac.NBId
import vc.data.AssigningSummary
import vc.data.TACCmd
import vc.data.TACSymbol

class LiveVariableAnalysis(private val graph: TACCommandGraph, val cmdFilter: ((LTACCmd) -> Boolean) = {_ -> true}) {

    private val lvars: Map<CmdPointer, Pair<TreapSet<TACSymbol.Var>, TreapSet<TACSymbol.Var>>>

    init {
        // First, compute the net effect each block has on the set of live variables, independent of other blocks.
        // We do this once per block, so that we don't have to compute the sets for each instruction in the worklist
        // iteration below.
        data class BlockSummary(
            val adds: TreapSet<TACSymbol.Var>,
            val removes: TreapSet<TACSymbol.Var>
        )
        val blockSummaries = graph.blocks.associate {
            val blk = graph.elab(it.id)
            var adds = treapSetOf<TACSymbol.Var>()
            var removes = treapSetOf<TACSymbol.Var>()
            for (c in blk.commands.asReversed()) {
                if (cmdFilter(c)) {
                    if (c.cmd is TACCmd.Simple.AssigningCmd) {
                        adds -= c.cmd.lhs
                        removes += c.cmd.lhs
                    }
                    if (c.cmd is TACCmd.Simple.SummaryCmd && c.cmd.summ is AssigningSummary) {
                        adds -= c.cmd.summ.mustWriteVars
                        removes += c.cmd.summ.mustWriteVars
                    }

                    val rhs = c.cmd.getFreeVarsOfRhsExtended()
                    adds += rhs
                    removes -= rhs
                }
            }
            it.id to BlockSummary(adds, removes)
        }

        // Bubble each block's effects through its predecessors.
        val blockPost = object : TACBlockDataflowAnalysis<TreapSet<TACSymbol.Var>>(
            graph = graph,
            bottom = treapSetOf(),
            lattice = JoinLattice.ofJoin { a, b -> a + b },
            direction = Direction.BACKWARD
        ) {
            override fun transform(inState: TreapSet<TACSymbol.Var>, block: TACBlock) =
                blockSummaries[block.id]!!.let { (adds, removes) ->
                    (inState - removes) + adds
                }
            init {
                runAnalysis()
            }
        }.blockIn

        // Now compute the live variables for each individual command.  Again, one pass per block.
        lvars = buildMap {
            for (b in graph.blocks) {
                var after = blockPost[b.id].orEmpty()
                for (c in b.commands.asReversed()) {
                    var before = after
                    if (cmdFilter(c)) {
                        if (c.cmd is TACCmd.Simple.AssigningCmd) {
                            before -= c.cmd.lhs
                        }
                        if (c.cmd is TACCmd.Simple.SummaryCmd && c.cmd.summ is AssigningSummary) {
                            before -= c.cmd.summ.mustWriteVars
                        }
                        before += c.cmd.getFreeVarsOfRhsExtended()
                    }
                    put(c.ptr, before to after)
                    after = before
                }
            }
        }
    }

    fun liveVariablesBefore(ptr: CmdPointer): Set<TACSymbol.Var> = lvars[ptr]?.first.orEmpty()
    fun liveVariablesBefore(block : NBId): Set<TACSymbol.Var> = lvars[CmdPointer(block, 0)]?.first.orEmpty()
    fun liveVariablesAfter(ptr: CmdPointer): Set<TACSymbol.Var> = lvars[ptr]?.second.orEmpty()

    fun isLiveAfter(ptr: CmdPointer, v: TACSymbol.Var): Boolean = (v in liveVariablesAfter(ptr))
    fun isLiveBefore(ptr: CmdPointer, v: TACSymbol.Var): Boolean = (v in liveVariablesBefore(ptr))
    fun isLiveBefore(block : NBId, v: TACSymbol.Var): Boolean = (v in liveVariablesBefore(block))
}
