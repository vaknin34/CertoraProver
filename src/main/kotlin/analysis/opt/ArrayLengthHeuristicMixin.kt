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

package analysis.opt

import analysis.CmdPointer
import analysis.PatternMatcher
import analysis.TACCommandGraph
import analysis.alloc.AllocationAnalysis
import analysis.maybeNarrow
import utils.firstMapped
import vc.data.TACCmd
import vc.data.TACKeyword
import vc.data.TACSymbol

interface ArrayLengthHeuristicMixin {
    /**
     * Indicates whether [v] at [where] in graph [g] is plausibly used as the length of an array that is being allocated.
     * If so, this function returns true, indicating that optimizations should not try to optimize
     * whatever computation involves [v] at [where]. Otherwise, it returns false. NB when this function
     * returns true, it is neither and overapproximation or underapproximation, i.e., it may return false
     * for variables that are the length component of an array allocation, or may spuriously return true. It is purely
     * best effort.
     */
    fun plausibleLengthComponent(g: TACCommandGraph, v: TACSymbol.Var, where: CmdPointer) : Boolean {
        val matcher = PatternMatcher.compilePattern(graph = g, patt = AllocationAnalysis.arrayCreationPattern)
        return g.iterateBlock(where, excludeStart = true).takeWhile {
            it.cmd.getLhs() != v
        }.firstMapped {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.takeIf {
                it.cmd.lhs == TACKeyword.MEM64.toVar()
            }
        }?.let {
            matcher.queryFrom(start = it).toNullableResult()
        }?.let {
            it.elemSym == where to v
        } == true
    }
}
