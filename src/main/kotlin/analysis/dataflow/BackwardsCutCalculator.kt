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

import algorithms.SimpleDominanceAnalysis
import algorithms.transitiveClosure
import com.certora.collect.*
import datastructures.ArrayHashSet
import datastructures.MultiMap
import datastructures.reverse
import datastructures.stdcollections.*
import utils.*


/**
 * Preprocess graph [g] so it is able to answer backward cut queries efficiently. Such a query gets a `query` vertex
 * and a set of `candidates` vertices. Traversing backwards from `query` in the graph (no matter in what fashion, DFS, BFS,
 * etc.), the traversal stops (does not continue backward) at vertices from `candidates` or when reaching a vertex that
 * has no predecessors.
 *
 * The result is the set of vertices from `candidates` that was encountered. `null` is also in the result if a
 * non-candidate vertex with no predecessors was reached.
 *
 * The intuition behind this (and the main use case) is def-analysis. Where `candidates` are all the known definition
 * sites of a variable. The `null` marks the case where the variable may be uninitialized.
 *
 * Note that the algorithm is not as described above, but is rather an optimized equivalent version.
 *
 * Queries can be done concurrently, as the state is immutable after initialization.
 * @param [reachability] is the transitive closure of `g` and can be given if it is already pre-computed.
 */
class BackwardsCutCalculator<@Treapable V : Any>(
    private val g: MultiMap<V, V>,
    reachability: MultiMap<V, V>?,
    domination: SimpleDominanceAnalysis<V>?,
) {
    private val dom = domination ?: SimpleDominanceAnalysis(g)
    private infix fun V.dominates(o: V) = dom.dominates(this, o)

    private val graphReachability = reachability ?: transitiveClosure(g, reflexive = false)
    private infix fun V.canReach(to: V) = graphReachability[this]?.contains(to) == true

    @Suppress("UNCHECKED_CAST")
    private val reversedGraph by lazy { reverse(g) as MultiMap<Any, Any> }

    /**
     * see documentation of [BackwardsCutCalculator], if [consume] returns true, the traversal is stopped and
     * the method exits early
     */
    fun backwardsCutFrom(query: V, candidates: Set<V>, consume: (V?) -> Boolean) {
        val filteredCandidates = if (candidates.size > 50) {
            // no filtering in this case
            candidates
        } else {
            val relevantCandidates = candidates.filterTo(mutableSetOf()) {
                it canReach query
            }

            if (relevantCandidates.isEmpty()) {
                consume(null)
                return
            }

            // Since domination is a tree, then if all candidates dominate `query`, then the last one is the answer.
            if (relevantCandidates.all { it dominates query && it != query }) {
                consume(
                    relevantCandidates.maxOfWith({ a: V, b: V ->
                        when {
                            a == b -> 0
                            a dominates b -> -1   // meaning a<=b, so higher up in the tree.
                            b dominates a -> 1
                            else -> error("Domination is not a tree??")
                        }
                    }) { it }
                )
                return
            }

            // it doesn't dominate,
            relevantCandidates.singleOrNull()?.let { c ->
                if (c != query) {
                    if (consume(null)) {
                        return
                    }
                    consume(c)
                    return
                }
                // if the single candidate is query, it may dominate or may not. So we fallback.
            }
            relevantCandidates
        }

        // All this casting to `Any` is to prevent expensive run time checks. In general, we'd rather not reach this
        // backwards traversal algorithm.

        val visited = ArrayHashSet<Any?>(127)
        val workList = ArrayDeque<Any?>(100)

        workList.addLast(reversedGraph[query])
        workList.consume {
            if (it == null) {
                if (consume(null)) {
                    return
                }
            } else {
                val set = it.uncheckedAs<Set<Any>>()
                if (set.isEmpty()) {
                    if (consume(null)) {
                        return
                    }
                } else {
                    var shouldReturn = false
                    set.forEachElement { b ->
                        if (visited.add(b)) {
                            if (b in filteredCandidates) {
                                shouldReturn = shouldReturn || consume(b.uncheckedAs())
                            } else {
                                workList.addLast(reversedGraph[b])
                            }
                        }
                    }
                    if (shouldReturn) {
                        return
                    }
                }
            }
        }
    }
}


/**
 * Same as [BackwardsCutCalculator], but works on a graph where each [B] node is actually a directed line graph,
 * indexed with ints. In other words, <[B], [Int]> is how nodes looks in the graph.
 *
 * @param [reachability] is the transitive closure of `g` and can be given if it is already pre-computed (to save time).
 * @param [domination] similarly, is the domination information for  `g`, not-null if pre-computed.
 */
class BlockBackwardsCutCalculator<@Treapable B : Any>(
    g: Map<B, Set<B>>,
    reachability: MultiMap<B, B>?,
    domination: SimpleDominanceAnalysis<B>?
) {
    private val cutCalculator = BackwardsCutCalculator(g, reachability, domination)

    /**
     * [block] and [pos] indicate the block and position within the block constituting the query point.
     * [candidates] is the set of candidates to choose from, and should be given as a **sorted** iterable of indices
     *    for each block.
     * [build] is a function to construct the result from each block-pos pair.
     */
    fun <T> backwardsCutFrom(
        block: B,
        pos: Int,
        candidates: Map<B, Iterable<Int>>,
        nullOnNull : Boolean,
        build: (B, Int) -> T,
    ): Set<T?>? {
        // if there is a candidate within the same block and before the query point.
        candidates[block]?.findLast { it < pos }?.let {
            return build(block, it).let {
                if (it == null && nullOnNull) {
                    null
                } else {
                    setOf(it)
                }
            }
        }
        // the last position in each of the blocks in the cut.
        val out = ArrayHashSet<T?>()
        cutCalculator.backwardsCutFrom(block, candidates.keys) { b ->
            val newElement = b?.let {
                build(b, candidates[b]!!.last())
            }
            out += newElement
            // stop if:
            nullOnNull && newElement == null
        }
        return out.takeUnless { nullOnNull && null in it }
    }
}
