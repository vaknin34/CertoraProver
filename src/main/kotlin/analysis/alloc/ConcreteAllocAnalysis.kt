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

import analysis.TACCommandGraph
import optimizer.FREE_POINTER_SCALARIZED
import utils.mapNotNull
import utils.parallelStream
import vc.data.TACCmd
import vc.data.TACKeyword
import vc.data.TACSymbol

typealias ConcreteAllocAnalysisResults = Boolean

/**
 * This is a shell of the previous implementation. Effectively this class simply returns a boolean flag (whether the
 * [ConcreteAllocAnalysisResults] value returned is non-null) to indicate whether we (heuristically) think the tac program
 * uses concrete offsets.
 */
object ConcreteAllocAnalysis {
    private fun hasConcreteAllocations(g: TACCommandGraph) : Boolean =
        g.commands.any { ltc ->
            ltc.cmd is TACCmd.Simple.AssigningCmd.ByteStore &&
                    ltc.cmd.base == TACKeyword.MEMORY.toVar() &&
                    ltc.cmd.loc is TACSymbol.Const
        }

    fun runAnalysis(graph: TACCommandGraph) : ConcreteAllocAnalysisResults {
        // If there is at least one FREE_POINTER_SCALARIZED annotation and all such annotations are false, then freePointerScalarized is false.  Otherwise, including if there are no FREE_POINTER_SCALARIZED annotations, default/set to true
        val freePointerScalarized = graph.commands.parallelStream().mapNotNull { ltc -> ltc.cmd.maybeAnnotation(FREE_POINTER_SCALARIZED) }.anyMatch { it }
        // If we don't have any concrete allocs or scratch sites, but the FP is not scalarized, this is a trivial concrete alloc function and we still need an init analysis
        return hasConcreteAllocations(graph) ||  !freePointerScalarized
    }
}
