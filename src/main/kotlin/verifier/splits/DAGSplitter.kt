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

import algorithms.*
import analysis.worklist.dagRunningFold
import com.certora.collect.*
import datastructures.*
import datastructures.stdcollections.*
import utils.containsAll
import utils.maxsWith


/**
 * Given a pivot (some vertex in the graph), we consider splitting the dag to two sub-graphs:
 *   1. The subgraph consisting only of paths that must go through the pivot.
 *   2. The subgraph consisting only of paths that don't go through the pivot.
 *
 * Paths start at a root vertex, and end in some [origSinks] vertex (which stand for block where there is an assert).
 * We assume that the original graph does not have vertices that can't lead to any [origSinks] (because this would mean
 * that there is no assert from that point on, and so why have it?). Specifically this means that every leaf in the DAG
 * is in [origSinks].
 *
 * This only matters in case 2, because it means that vertices that can only lead to the erased pivot, should still
 * remain in the graph if they can still lead to a vertex in [origSinks].
 *
 * Note that there are hardly any calculations on initialization. They only happen within the functions.
 */
class DAGSplitter<@Treapable V : Any>(
    private val g: MultiMap<V, V>,
    private val origSinks: Set<V>,
) {
    private val vertices = g.keys

    data class Result<V, S>(
        val pivot: V,
        val scoreIfPassing: S,
        val scoreIfNotPassing: S,
    )

    /**
     * This is meant to check cheaply (without going into transitive closure and domination calculations), whether
     * there is a non-trivial split in this graph, i.e., a split which removes at least one vertex on each side.
     *
     * The `dontPass` version always erases at least one vertex, but we want to see that the `mustPass` version also
     * does (at least for one vertex).
     *
     * The key observation is that the graph contains a hamiltonian path (that goes through all vertices) iff the
     * the graph is unsplittable (i.e., the `mustPass` of every vertex doesn't remove anything).
     *
     * ==> If there is a hamiltonian path, then no matter what vertex we "force" (i.e., must go though), this path still
     * remains in the graph, and so no other vertex is removed.
     *
     * <== if the graph is unsplittable, then take a topological ordering of the vertices. Looking at the `mustPass` of
     * the vertex at `i`, we know it does not remove the vertex at `i+1`. But edges can't "jump" over `i` (because we
     * must pass through it), and therefore there must be an edge from `i` to `i+1`. So the topological order is a
     * hamiltonian path.
     *
     * The proof also gives the way to check for a hamiltonian path in a DAG. Take any topological order and see that
     * each vertex is connected to the next.
     */
    fun isSplittable(): Boolean {
        val topOrder = topologicalOrder(g).reversed()
        topOrder.zipWithNext().forEach { (u, v) ->
            if (g[u].orEmpty().none { it == v }) {
                return true
            }
        }
        return false
    }


    /**
     * Returns the list of pivots with the highest scores, and the [SideScore] one would get if all vertices were removed.
     *
     * For each vertex, it calculates the score of the vertices that are removed. Recalling that the set of leaves
     * is contained in [origSinks], then the removed vertices are:
     *   1. If we must pass through the pivot, then the remaining vertices are those that can reach the pivot
     *      and those that the pivot can reach.
     *   2. If we mustn't pass through it, then the deleted vertices are those dominated by the pivot in the forward
     *      graph, plus those that dominated by it in the backwards graph, except [origSinks] and those that can reach
     *      them.
     */
    fun <S : SideScore<S>> bestPivots(scorer: SplitScorer<V, S>): Pair<List<Result<V, S>>, S> {
        val scoreMap = vertices.associateWith(scorer::ofOne)
        fun score(v: V) = scoreMap[v]!!
        fun addScores(a: S, b: S) = a + b

        val t = transitiveClosure(g, reflexive = true)

        val reachForwardScore = mutableMapOf<V, S>()
        val reachBackwardScore = mutableMapOf<V, S>()
        t.pairsSeq.forEach { (i, j) ->
            reachForwardScore.merge(i, score(j), ::addScores)
            reachBackwardScore.merge(j, score(i), ::addScores)
        }

        fun calcDomScores(graph: MultiMap<V, V>) =
            reverseMap(SimpleDominanceAnalysis(graph).immediatelyDominatedBy)
                .dagRunningFold(::score, ::addScores, vertices)

        val domScore = calcDomScores(g)

        val revDomScore = run {
            // backwards domination, but stopping at [origLeaves].
            val revG = buildMultiMap {
                g.pairsSeq.forEach { (u, v) ->
                    if (u !in origSinks) {
                        add(v, u)
                    }
                }
            }
            calcDomScores(revG)
        }

        val globalScore = scoreMap.values.reduce(::addScores)

        fun scoreMustPass(v: V): S {
            val remain = reachBackwardScore[v]!! + reachForwardScore[v]!! - score(v)
            // let's include the number of edges that can be cut?
            return globalScore - remain
        }

        fun scoreDontPass(v: V): S =
            domScore[v]!! + revDomScore[v]!! - score(v)

        val results = vertices.map { Result(it, scoreMustPass(it), scoreDontPass(it)) }
            .maxsWith { result1, result2 ->
                scorer.comparePair(
                    Pair(result1.scoreIfPassing, result1.scoreIfNotPassing),
                    Pair(result2.scoreIfPassing, result2.scoreIfNotPassing)
                )
            }
        return results to globalScore
    }
}


/**
 * Keep a graph constrained to paths that go through all vertices in [mustPass], don't go through vertices
 * in [dontPass], and can reach a vertex in [origSinks] (but only after passing through all of [mustPass]).
 * In our usage for program splitting, [origSinks] stand for the blocks where there are assert commands.
 *
 * note that the [mustPass] must have some path going through all of them. So in topological order there is a
 * clear consistent order to them (no matter what is the topological order).
 *
 * We make sure here that all vertices have keys in the resulting map (even if the value is an empty set).
 */
fun <@Treapable V : Any> cutDAG(
    root: V,
    origGraph: MultiMap<V, V>,
    mustPass: Set<V>,
    dontPass: Set<V>,
    origSinks: Set<V>,
): MultiMap<V, V> {
    if (root in dontPass) {
        return emptyMap()
    }

    // first cleanup.
    val (vertices, g) = reachableSubgraph(origGraph, setOf(root)) { it !in dontPass }

    require(vertices containsAll mustPass) {
        // actually, in this case we should return an empty graph. However, for our use case this should never
        // happen, and so for safety, we crash.
        "cutting a DAG with contradicting parameters, resulting in an empty graph."
    }

    val sinks = origSinks intersect vertices
    val gRev = reverse(g)

    val top = topologicalOrder(root, g).reversed() // root first
    val indexOf = top.withIndex().associate { (i, v) -> v to i }
    fun indexOf(v: V) = indexOf[v]!!
    val mustsInOrder = listOfNotNull(root.takeIf { it !in mustPass }) + top.filter { it in mustPass }

    /**
     * The set of vertices that are reachable from [start] and can reach a vertex of [finish].
     * The result is inclusive of the end points, unless they don't satisfy the requirement themselves, e,g.,
     * only vertices of [finish] that are reachable from [start] are included.
     */
    fun verticesBetween(start: V, finish: Set<V>): Set<V> {
        val startI = indexOf(start)
        val relevantFinish = finish.filter { indexOf(it) >= startI }
        val backReach = getReachable(relevantFinish) { v ->
            gRev[v]?.filter {
                indexOf(it) >= startI
            }
        }
        if (start !in backReach) {
            return setOf()
        }
        val result = getReachable1(start) { v ->
            g[v]?.filter {
                it in backReach
            }
        }
        return result
    }

    // The resulting graph consists of "chunks" between the `musts`, and these chunks can't have any direct edges
    // between them, i.e., they can't "skip" a `must`.
    // after the last `must`, any vertex that can reach a `sink` is good.
    val chunks =
        mustsInOrder.zipWithNext().map { (x, y) -> verticesBetween(x, setOf(y)) } +
            listOf(verticesBetween(mustsInOrder.last(), sinks))

    if (chunks.any { it.isEmpty() }) {
        return emptyMap()
    }
    return buildMap {
        for (c in chunks) {
            for (v in c) {
                this[v] = g[v]?.filter { it in c }?.toSet().orEmpty()
            }
        }
    }
}

