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

package datastructures

import com.certora.collect.*
import datastructures.*
import datastructures.stdcollections.*
import utils.*

/**
 * As a map of sets, represents the successors or predecessors of each node in a graph.  [asReversed] returns a map with
 * the edge directions reverseMap. Changes to the "forward" map also update the "reverseMap" map, and vice versa.
 */
interface ReversibleDigraph<T> : Map<T, TreapSet<T>> {
    fun asReversed() : ReversibleDigraph<T>

    val forward: LinkedArrayHashMapReader<T, TreapSet<T>>
    val reverse: LinkedArrayHashMapReader<T, TreapSet<T>>
}

@Suppress("PARAMETER_NAME_CHANGED_ON_OVERRIDE") // We do this intentionally for clarity
class MutableReversibleDigraph<@Treapable T> private constructor(
    private val forwardMap: LinkedArrayHashMap<T, TreapSet<T>>,
    private val reverseMap: LinkedArrayHashMap<T, TreapSet<T>>
) : MutableMap<T, TreapSet<T>> by forwardMap, ReversibleDigraph<T>, java.io.Serializable {

    constructor() : this(LinkedArrayHashMap(), LinkedArrayHashMap())
    constructor(map: Map<T, TreapSet<T>>) : this(forwardMap = makeForwardMap(map), reverseMap = makeReverseMap(map))
    override fun asReversed() = MutableReversibleDigraph<T>(forwardMap = reverseMap, reverseMap = forwardMap)

    override fun equals(other: Any?) = forwardMap.equals(other)
    override fun hashCode() = forwardMap.hashCode()
    override fun toString() = forwardMap.toString()

    override val forward: LinkedArrayHashMapReader<T, TreapSet<T>> get() = forwardMap
    override val reverse: LinkedArrayHashMapReader<T, TreapSet<T>> get() = reverseMap

    override fun clear() {
        forwardMap.clear()
        reverseMap.clear()
    }

    /** Add or update [node] */
    override fun put(node: T, newForward: TreapSet<T>): TreapSet<T>? {
        val oldForwardIfPresent = forwardMap.put(node, newForward)

        val oldForward = oldForwardIfPresent.orEmpty()
        val addedForward = newForward - oldForward
        val removedForward = oldForward - newForward

        addedForward.forEach {
            reverseMap.addEdge(from = it, to = node)
            // Ensure the forward node is in [forwardMap], even if it doesn't have forward edges
            forwardMap.getOrPut(it) { treapSetOf() }
        }
        removedForward.forEach {
            reverseMap.removeEdge(from = it, to = node)
        }

        // Ensure the node is in [reverseMap], even if it doesn't have reverse edges
        reverseMap.getOrPut(node) { treapSetOf() }

        return oldForward
    }

    /** Remove [node] and return its (former) forward edge set */
    override fun remove(node: T): TreapSet<T>? {
        val oldForward = forwardMap.remove(node)
        if (oldForward != null) {
            finishRemovingNode(node, oldForward)
        }
        return oldForward
    }

    /** Remove [node] iff it's forward edges are exactly [oldForward] */
    override fun remove(node: T, oldForward: TreapSet<T>): Boolean {
        if (forwardMap.remove(node, oldForward)) {
            finishRemovingNode(node, oldForward)
            return true
        } else {
            return false
        }
    }

    /** After [node]'s entry was removed from [forwardMap], update the rest of both maps' entries */
    private fun finishRemovingNode(node: T, oldForward: TreapSet<T>) {
        // remove the node from the reverse map
        val oldReverse = reverseMap.remove(node).orEmpty()

        // remove all edges into and out of the node
        oldReverse.forEach {
            forwardMap.removeEdge(from = it, to = node)
        }
        oldForward.forEach {
            reverseMap.removeEdge(from = it, to = node)
        }
    }

    //
    // We have to build our own Entry set, rather than delegating to `forwardMap.entries`, because we need to override the
    // `remove` function on the iterator object.
    //
    private inner class EntryIterator : MutableIterator<MutableMap.MutableEntry<T, TreapSet<T>>> {
        val keyIterator = forwardMap.keys.toList().iterator()
        var currentKey: T? = null
        override fun hasNext() = keyIterator.hasNext()
        override fun next(): MutableMap.MutableEntry<T, TreapSet<T>> {
            currentKey = keyIterator.next()
            return MutableMapEntry(this@MutableReversibleDigraph, currentKey.uncheckedAs<T>())
        }
        override fun remove() {
            this@MutableReversibleDigraph.remove(currentKey)
        }
    }

    private inner class EntrySet : AbstractMutableSet<MutableMap.MutableEntry<T, TreapSet<T>>>() {
        override val size get() = this@MutableReversibleDigraph.size
        override fun clear() = this@MutableReversibleDigraph.clear()
        override fun add(element: MutableMap.MutableEntry<T, TreapSet<T>>): Boolean = throw UnsupportedOperationException()
        override fun iterator(): MutableIterator<MutableMap.MutableEntry<T, TreapSet<T>>> = EntryIterator()
    }

    override val entries: MutableSet<MutableMap.MutableEntry<T, TreapSet<T>>> get() = EntrySet()

    companion object {
        /**
         * Builds a mutable copy of [map], ensuring that all nodes have a forward mapping
         */
        private fun <@Treapable T> makeForwardMap(map: Map<T, TreapSet<T>>): LinkedArrayHashMap<T, TreapSet<T>> {
            val forwardMap = LinkedArrayHashMap(map)
            map.forEachEntry { (_, forward) ->
                forward.forEach {
                    forwardMap.computeIfAbsent(it) { treapSetOf() }
                }
            }
            return forwardMap
        }

        /**
         * Builds a reverseMap graph.  We use TreapSets so that the operators in the methods above will
         * not have to do the conversion.
         */
        private fun <@Treapable T> makeReverseMap(map: Map<T, TreapSet<T>>): LinkedArrayHashMap<T, TreapSet<T>> {
            val reverseMap = LinkedArrayHashMap<T, TreapSet<T>>()
            map.forEachEntry { (node, forward) ->
                forward.forEach {
                    reverseMap[it] = reverseMap[it].orEmpty() + node
                }
            }
            map.forEachEntry { (node, _) ->
                unused(reverseMap.computeIfAbsent(node) { treapSetOf() })
            }
            return reverseMap
        }

        private fun <@Treapable T> MutableMap<T, TreapSet<T>>.addEdge(from: T, to: T) {
            this[from] = this[from].orEmpty() + to
        }

        private fun <@Treapable T> MutableMap<T, TreapSet<T>>.removeEdge(from: T, to: T) {
            val set = this[from]
            if (set != null) {
                this[from] = set - to
            }
        }
    }
}
