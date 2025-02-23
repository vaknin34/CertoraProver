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

package analysis.storage

import analysis.*
import analysis.pta.ITERATION_VARIABLE_BOUND
import utils.firstMapped
import utils.`to?`
import vc.data.TACExpr
import java.math.BigInteger

/**
 * See [StorageLoopPeeler] for the motivation for this module.
 *
 * This heuristic is based on observed code patterns, so we're looking for
 *
 * Head:
 *    ::ITERATION_VARIABLE_BOUND(iterationVar=i, bound=b, stride=k)
 *    ...
 *    goto Tail
 *
 * Tail:
 *    ...
 *    goto Head
 *
 * where at Head,
 *   b \def ((b_0 + 0x20) + 0x1f) >> 5
 *   i \def 0
 */
open class VyperPeelStorageHeuristic(val graph: TACCommandGraph): IStorageLoopPeelHeuristic {
    private val boundComputationPattern = PatternDSL.build {
        (((Var + 32()).commute + 31()).commute `shrLogical` 5()).second
    }

    private val matcher = PatternMatcher.compilePattern(graph, boundComputationPattern)

    override fun shouldPeelIteration(loop: Loop): Boolean {
        val (iterBoundLoc, iterBound) = graph.elab(loop.head).commands.firstMapped {
            it.ptr `to?` it.maybeAnnotation(ITERATION_VARIABLE_BOUND)
        } ?: return false

        if (iterBound.stride != BigInteger.ONE) {
            return false
        }

        val initToZero = graph.cache.def
            .defSitesOf(iterBound.iterationVariable, iterBoundLoc)
            .singleOrNull { it.block !in loop.body }
            ?.let { def ->
                graph.elab(def).maybeExpr<TACExpr.Sym.Const>()?.exp?.getAsConst() == BigInteger.ZERO
            } == true

        if (!initToZero) {
            return false
        }

        val matchBoundDef = matcher.query(iterBound.boundVariable, graph.elab(iterBoundLoc)) is PatternMatcher.ConstLattice.Match

        if (!matchBoundDef) {
            return false
        }

        return true
    }
}
