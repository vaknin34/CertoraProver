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

package verifier.splits

import cli.SplitHeuristicEnum
import config.Config
import datastructures.stdcollections.*
import log.*
import utils.Color.Companion.blue
import utils.Color.Companion.red
import utils.Color.Companion.yellow
import vc.data.CoreTACProgram
import verifier.splits.SplitAddress.Block

private val logger = Logger(LoggerTypes.SPLIT)

/**
 * Uses [DAGSplitter] to split the [node].
 */
class PivotSplitter(private val node: SplitTree.Node) : Splitter {
    private val lazySub get() = node.lazySub

    private fun graphSplitter(actualTAC: CoreTACProgram) =
        DAGSplitter(actualTAC.analysisCache.graph.blockSucc, lazySub.assertBlocks)

    override fun splittable(actualTAC: CoreTACProgram) =
        graphSplitter(actualTAC).isSplittable()

    override fun split(actualTAC: CoreTACProgram) =
        with(node) {
            require(splittable) { "Can only split a splittable split" }

            val splitter = graphSplitter(actualTAC)
            val scorer = when (Config.SplitHeuristic.get()) {
                SplitHeuristicEnum.NON_LINEAR -> NLScorer(actualTAC)
                SplitHeuristicEnum.SIZE_ONLY -> SizeScorer
            }
            val (pivotResults, globalScore) = splitter.bestPivots(scorer)
            // use the block names to give a consistent result across runs.
            val pivotResult = pivotResults.maxBy { it.pivot.toString() }
            logger.info {
                "${address.red}[global=${globalScore.yellow}] --- ${pivotResult.blue}"
            }
            with(pivotResult) {
                setChildren(
                    listOf(
                        Block.MustPass(address, pivot) to scoreIfPassing,
                        Block.DontPass(address, pivot) to scoreIfNotPassing
                    )
                )
            }
        }

}

