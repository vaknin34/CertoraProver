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

import analysis.icfg.ExpressionSimplifier
import analysis.narrow
import log.*
import utils.parallelStream
import vc.data.CoreTACProgram
import vc.data.TACCmd
import java.math.BigInteger
import java.util.stream.Collectors
import java.util.stream.Stream
import tac.MetaMap
import vc.data.TACMeta
import vc.data.TACSymbol

private val logger = Logger(LoggerTypes.PRUNING)

open class Pruner(private val c: CoreTACProgram) {
    private val g = c.analysisCache.graph
    open protected val simplifier = ExpressionSimplifier(g, g.cache.def)
    private val mut = c.toPatchingProgram()

    open val stopAt: ((TACSymbol.Var) -> Boolean) ? = null

    fun prune(): CoreTACProgram {
        unreachablePathPruning()
        return mut.toCode(c)
    }


    /**
     * Prunes unreachable paths by resolving conditional jumps and removing unreachable edges,
     * and subgraphs in case the target of the removed edge becomes unreachable.
     */
    private fun unreachablePathPruning() {
        val edges = g.commands.parallelStream().filter { it.cmd is TACCmd.Simple.JumpiCmd }.map {
            it.narrow<TACCmd.Simple.JumpiCmd>()
        }.flatMap { jumpiCmd ->
            val condSimplified = simplifier.simplify(jumpiCmd.cmd.cond, jumpiCmd.ptr, true, stopAt).getAsConst()
            if (condSimplified != null) {
                Stream.of(jumpiCmd to (condSimplified != BigInteger.ZERO))
            } else {
                Stream.empty()
            }
        }.collect(Collectors.toList())

        fun getSourceFromCommand(meta: MetaMap): String {
            return meta[TACMeta.CVL_RANGE]?.toString() ?: "Missing source reference information"
        }

        if (edges.isNotEmpty()) {
            logger.debug { "Pruning edges $edges" }

            edges.map{ getSourceFromCommand(it.first.wrapped.cmd.meta)}
                .forEach{ Logger.regression {"For CVL If command at $it it was found that only one branch was needed"}}

            mut.selectConditionalEdges(edges)
        }
    }
}

