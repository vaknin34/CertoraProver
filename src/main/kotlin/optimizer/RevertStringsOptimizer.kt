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

package optimizer

import algorithms.getReachable
import analysis.EthereumVariables.simplifyRevert
import vc.data.TACSymbol
import allocator.Allocator
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACKeyword
import vc.data.TACRevertType
import java.util.stream.Collectors

/**
 * Replaces subgraphs used to copy strings (or otherwise something interesting) as revert messages with a single sink node that has a revert with no data.
 */
object RevertStringsOptimizer {
    fun optimizeRevertStrings(code: CoreTACProgram): CoreTACProgram {
        val g = code.analysisCache.graph
        val patch = code.toPatchingProgram()
        /*val revertBlocks = code.analysisCache.revertBlocks*/ // not returning the blocks wanted here

        val reverting = g.sinkBlocks
            .filter {
                it.commands.last()
                    .let { lst ->
                        lst.cmd is TACCmd.Simple.RevertCmd &&
                                lst.cmd.revertType == TACRevertType.BENIGN
                    }
            }
            .map { it.id }
            .toMutableList()

        val sinks = g.sinkBlocks.map { it.id }
        // get blocks that reach only sink blocks that are reverting (i.e., if reach a non-reverting sink, it is not a revert block)
        val revertBlocks = g.blocks
            .map { it.id }
            .filter {
                getReachable(it, code.blockgraph).let { reach ->
                    reach.all { r ->
                        // r in sink => r in reverting
                        r !in sinks || r in reverting
                    }
                }
            }


        // for a revert block with predecessor that is not a revert block, and with successors, and that is not the root,
        // replace it with a simple revert command of size 0 as in the reaching leaf.
        val revertBlocksToConsolidate = revertBlocks
            .parallelStream()
            .filter { revertBlock ->
                g.pred(revertBlock).all { it !in revertBlocks } && // all predecessors are not reverting
                        g.succ(revertBlock).isNotEmpty() && // has successors
                        revertBlock !in g.rootBlocks.map { it.id } // not the root because we're not that brave (TODO although why not?)
            }
            .sequential()
            .collect(Collectors.toList())

        if (revertBlocksToConsolidate.isEmpty()) {
            return code // nothing to do
        }

        val revert = simplifyRevert(
            TACCmd.EVM.EVMRevertCmd(TACSymbol.lift(0), TACSymbol.lift(0), TACRevertType.BENIGN, TACKeyword.MEMORY.toVar())
        )
        val newBlockId =
            patch.addBlock(
                Allocator.getNBId(),
                revert.cmds
            )

        patch.addVarDecls(revert.varDecls)

        patch.consolidateEdges(
            newBlockId,
            revertBlocksToConsolidate
        )
        return patch.toCode(code)
    }
}