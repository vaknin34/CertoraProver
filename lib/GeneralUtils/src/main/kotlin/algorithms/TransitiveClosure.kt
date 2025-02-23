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

package algorithms

import com.certora.collect.*
import datastructures.ArrayHashMap
import datastructures.reverseMap
import datastructures.stdcollections.*
import utils.arrayDequeOf
import utils.consume

/**
 * Computes the transitive closure of each node in a directed graph.  Takes great care to lay out the resulting
 * Set data structures such that they share memory as much as possible, so that we can feasibly retain the transitive
 * closures for non-trivial graphs.
 */
fun <@Treapable V> transitiveClosure(
    graph: Map<V, Set<V>>,
    reflexive: Boolean = false,
): Map<V, TreapSet<V>> = mapTransitiveClosure(graph, reflexive) { v -> v.toTreapSet() }.toMap()

fun <@Treapable V, @Treapable R> mapTransitiveClosure(
    graph: Map<V, Set<V>>,
    reflexive: Boolean = false,
    transform: (Set<V>) -> TreapSet<R>
) = sequence<Pair<V, TreapSet<R>>> {

    // To maximize memory sharing, we first partition the graph into its strongly-connected components.  Every
    // node in a given SCC will have the same transitive closure, and so we can share the resulting sets completely
    // between those nodes.  Since the SCC graph is a DAG, we can then further maximize sharing by building up
    // the closures in reverse-topological order, using PersistentSets to produce unions that share memory with
    // successors' closures.

    val sccReflexiveClosures = ArrayHashMap<Int, TreapSet<R>>()
    val scc = SCCGraph(graph)
    for (sccIndex in topologicalOrder(scc.sccGraph)) {
        // Build the non-reflexive closure of this SCC
        val nonReflexiveClosure = scc.sccGraph[sccIndex]?.fold(treapSetOf<R>()) { s, i ->
            s + sccReflexiveClosures[i]!!
        }.orEmpty()

        // Add in the results from this SCC, to make the reflexive closure
        val sccNodes = scc.sccs[sccIndex]!!
        val reflexiveClosure = nonReflexiveClosure + transform(sccNodes)
        sccReflexiveClosures[sccIndex] = reflexiveClosure

        // Assign closures to the nodes in this SCC. If we are building non-reflexive result closures, and this SCC
        // contains just one node, and that node does not have an edge to itself, then we use the non-reflexive SCC
        // closure.  Otherwise we use the reflexive one.
        if (!reflexive) {
            val singleNode = sccNodes.singleOrNull()
            if (singleNode != null) {
                if (singleNode in graph[singleNode].orEmpty()) {
                    yield(singleNode to reflexiveClosure)
                } else {
                    yield(singleNode to nonReflexiveClosure)
                }
                continue
            }
        }
        sccNodes.forEach { node ->
            yield(node to reflexiveClosure)
        }
    }
}


/**
 * Calculates the transitive closure of a tree via DFS traversal. In the DFS, the number of steps is counted, and each
 * vertex is marked with the step number when it was entered, and the one where it exited. Then `x` is an ancestor
 * of `y` iff the interval `(entry(x), exit(x))` contains the interval `(entry(y), exit(y))`
 *
 * The transitive closure is saved implicitly, and as said, this is enough to answer ancestor queries in O(1) time. To
 * Answer set queries such as [allAncestors], we generate the set on the fly as its a linear process, and saves us the
 * need to keep all sets.
 *
 * If needed, this can be extended to support forests. However, this trick does not support DAGs at all.
 */
class TreeTransitiveClosure<@Treapable V : Any>(private val parent: Map<V, V>) {
    private val root = parent.values
        .filter { parent[it] == null }
        .distinct()
        .singleOrNull()
        ?: error("A tree is supposed to have exactly one root")
    private val children = reverseMap(parent)

    private val entry = mutableMapOf<V, Int>()
    private val exit = mutableMapOf<V, Int>()

    init {
        var num = 0
        deRecurse(
            start = root,
            pre = {
                entry[it] = num++
                true
            },
            post = {
                exit[it] = num++
            },
            nexts = {
                children[it]?.iterator()
            }
        )
    }

    /** true if [v1] is an ancestor of [v2] (reflexively) */
    fun isAncestor(v1: V, v2: V) =
        entry[v1]!! <= entry[v2]!! && exit[v1]!! >= exit[v2]!!

    /** true if [v1] is a descendant of [v2] (reflexively) */
    fun isDescendant(v1: V, v2: V) =
        isAncestor(v2, v1)

    fun allAncestors(v: V): Set<V> =
        treapSetBuilderOf<V>().also { set ->
            var c: V? = v
            while (c != null) {
                set += c
                c = parent[c]
            }
        }.build()

    fun allDescendents(v: V): Set<V> =
        treapSetBuilderOf<V>().also { set ->
            val queue = arrayDequeOf(v)
            queue.consume {
                set += it
                queue += children[it].orEmpty()
            }
        }.build()

}


