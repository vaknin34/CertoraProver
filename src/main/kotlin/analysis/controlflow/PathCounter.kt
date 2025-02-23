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

package analysis.controlflow

import algorithms.getReachable
import analysis.TACCommandGraph
import analysis.worklist.volatileDagDataFlow
import datastructures.stdcollections.*
import log.*
import tac.CallId
import tac.NBId
import utils.filterToSet
import java.math.BigInteger

/**
 * Calculates the amount of path exiting a specific block in the [graph], given via [blocksOfInterest].
 * Default for [blocksOfInterest] is "all nodes in the graph", note that usually this is memory-wasteful.
 *
 * Note that there would be room for optimization for our typical usages (computing things for a graph and many
 * combinations of subgraphs) here by giving a set of [callIdsToJump]-sets, and computing the results for all at once.
 * But I'm not sure it's worth it..
 */
class PathCounter(
    private val graph: TACCommandGraph,
    private val blocksOfInterest: Set<NBId> = graph.blockIds,
    private val callIdsToJump: Set<CallId> = emptySet(),
) {
    constructor(
        graph: TACCommandGraph,
        blockOfInterest: NBId,
        callIdsToJump: Set<CallId> = emptySet(),
    ) : this(graph, setOf(blockOfInterest), callIdsToJump)

    /**
     * Holds how many paths exist in the sub-DAG of a block.
     * Note this only holds entries for blocks given in [blocksOfInterest]
     */
    val pathCounts: Map<NBId, BigInteger>

    /** Returns the path count at the single block of interest that was given.
     * Will throw if [blocksOfInterest] has more than one element. */
    val singlePathCount : BigInteger get() {
        require(blocksOfInterest.size == 1) { "only call this when there is a single block of interest (got: $blocksOfInterest)"}
        val res = pathCounts[blocksOfInterest.single()]
        check(res != null) { "path count for block of interest $blocksOfInterest not computed" }
        return res
    }

    init {
        check(blocksOfInterest.isNotEmpty()) { "Doesn't make sense to run path counter with empty 'blocksOfInterest' parameter." }
        pathCounts = runAnalysis()
    }

    /** Compute successors of node [node] in graph [graph], but skip (or jump over) all nodes that have a call id that
     * appears in [callIdsToJump]. If [callIdsToJump] is empty, this acts like the regular successor
     * [TACCommandGraph.succ] function. */
    private fun jumpSuccessors(node: NBId): Set<NBId> {
        fun nx(n : NBId) = graph.succ(n).filter { it.calleeIdx in callIdsToJump }
        val jumpedNodes = getReachable(nx(node), ::nx)
        return (jumpedNodes + node).flatMap { n: NBId -> graph.succ(n) }.filterToSet { it.calleeIdx !in callIdsToJump }
    }


    /**
     * Goes through the graph from the sinks (0 successors), and calculates how many paths we saw in the successors.
     * For sinks, it will be 1 path (a "NOP" of sorts). For other blocks it will be the sum of their children.
     * This is a linear time analysis, but is not a normal DFS.
     * Some blocks will be "stuck" until all their children were processed (this assumes no cycles).
     */
    private fun runAnalysis(): Map<NBId, BigInteger> {
        val counts: MutableMap<NBId, BigInteger> = mutableMapOf()
        volatileDagDataFlow(
            graph.blockGraph.keys.filterToSet { it.calleeIdx !in callIdsToJump },
            ::jumpSuccessors
        ) { node, succResults : List<BigInteger> ->
            val r = if (succResults.isEmpty()) {
                BigInteger.ONE
            } else {
                succResults.sumOf { it }
            }
            if (node in blocksOfInterest) {
                counts[node] = r
            }
            r
        }
        return counts
    }
}
