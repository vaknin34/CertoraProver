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
import datastructures.stdcollections.*
import utils.*

object TarjanSCCFinding {
    class Node<T>(val t: T) {
        var index: Int? = null
        var lowLink: Int? = null
        var onStack: Boolean? = null

        override fun toString(): String {
            return "Node(t=$t,index=$index,lowLink=$lowLink,onStack=$onStack)"
        }
    }

    /**
     * thanks wiki I love u [https://en.wikipedia.org/wiki/Tarjan%27s_strongly_connected_components_algorithm]
     * An iterative version of the above.
     */
    fun <@Treapable T> tarjanSCCFinding(g: Map<T, Set<T>>): Set<TreapSet<T>> {
        val sccs = mutableSetOf<TreapSet<T>>()
        var index = 0
        val stack = mutableListOf<Node<T>>()
        val allNodes = g.keys.toMutableSet()
        g.values.forEach { succs ->
            succs.forEach { succ -> allNodes.add(succ) }
        }
        val V = allNodes.map { it to Node(it) }.toMap()

        fun strongconnect(v_: Node<T>) {
            val recursionStack = mutableListOf<Pair<Node<T>, Int>>()
            var recurse: Boolean
            recursionStack.add(v_ to 0)
            while (recursionStack.isNotEmpty()) {
                val (v, i) = recursionStack.removeAt(0)
                if (i == 0) {
                    v.index = index
                    v.lowLink = index
                    index += 1
                    stack.add(v)
                    v.onStack = true
                }
                recurse = false
                val cont = (g[v.t] ?: emptySet()).map { V[it]!! }
                for (j in cont.indices) {
                    if (j >= i) {
                        val w = cont[j]
                        if (w.index == null) {
                            recursionStack.add(0, v to j + 1)
                            recursionStack.add(0, w to 0)
                            recurse = true
                            break
                        } else if (w.onStack == true) {
                            v.lowLink = Math.min(v.lowLink!!, w.index!!)
                        }
                    }
                }

                if (recurse) {
                    continue
                }
                if (v.lowLink == v.index) {
                    val scc = treapSetBuilderOf<T>()
                    do {
                        val w = stack.removeAt(stack.size - 1)
                        w.onStack = false
                        scc.add(w.t)
                    } while (w.t != v.t)
                    sccs.add(scc.build())
                }
                if (recursionStack.isNotEmpty()) {
                    val w = v
                    val (v__, _) = recursionStack[0]
                    v__.lowLink = Math.min(v__.lowLink!!, w.lowLink!!)
                }
            }
        }

        V.values.forEach { v ->
            if (v.index == null) {
                strongconnect(v)
            }
        }

        return sccs
    }

}

/**
 * A wrapper around [TarjanSCCFinding.tarjanSCCFinding] that creates and holds scc graph and not only the classes
 */
open class SCCGraph<@Treapable T>(g: Map<T, Set<T>>) {
    val nodeToSccIndex: Map<T, Int>
    val sccs: Map<Int, TreapSet<T>>
    val sccGraph: Map<Int, TreapSet<Int>>

    init {
        nodeToSccIndex = mutableMapOf()
        sccs = mutableMapOf()

        TarjanSCCFinding.tarjanSCCFinding(g).forEachIndexed { sccIndex, scc ->
            sccs[sccIndex] = scc
            scc.forEach {
                nodeToSccIndex[it] = sccIndex
            }
        }

        // build scc graph
        sccGraph = mutableMapOf()
        sccs.entries.associateTo(sccGraph) { (index, component) ->
            val toRet = treapSetBuilderOf<Int>()
            component.forEach { node ->
                g[node]?.mapNotNullTo(toRet) { succ ->
                    val targetScc = nodeToSccIndex[succ]?.takeIf {
                        it != index
                    } ?: return@mapNotNullTo null
                    targetScc
                }
            }
            index to toRet.build()
        }
    }

    /** Roots in scc graph are the indices that have no predecessors */
    val rootSccs: Set<Int> by lazy { sccGraph.keys - sccGraph.values.flatten() }

    val roots: Set<T> by lazy {
        rootSccs.flatMapTo(mutableSetOf()) { sccs[it]!! }
    }

    /** Sinks in scc graph are the indices that have no successors */
    val leafSccs: Set<Int> by lazy {
        sccs.keys.filter {
            sccGraph[it].isNullOrEmpty()
        }.toSet()
    }

    val leaves: Set<T> by lazy {
        leafSccs.flatMapTo(mutableSetOf()) { sccs[it]!! }
    }
}

/**
    Extends [SCCGraph] to include methods for answering questions about the original graph.  This is a separate class so
    that SCCGraph does not have to track the (potentially large) original graph.
 */
open class SCCGraphInfo<@Treapable T>(val g: Map<T, Set<T>>) : SCCGraph<T>(g) {
    /** All components are of size 1 and there are no self loops */
    val isDag: Boolean by lazy {
        sccs.values.all { it.size == 1 } && !g.keys.any { g[it]?.contains(it) == true }
    }

    /** [t]'s Component size is more than 1, or [t] has a self loop. */
    fun isInLoop(t: T) =
        sccs[nodeToSccIndex[t]!!]!!.size > 1 || g[t]?.contains(t) == true
}

/**
 * Finds the set of roots in a directed graph [g].
 */
fun <@Treapable T> findRoots(g: Map<T, Set<T>>) = SCCGraph(g).roots
