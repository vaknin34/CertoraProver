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
import datastructures.MultiMap
import datastructures.pairs
import datastructures.stdcollections.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class TransitiveClosureTest {

    fun Map<Char, Set<Char>>.closedSuccTo(result: MutableSet<Char>, node: Char, includeNode: Boolean): Set<Char> {
        if (includeNode) result.add(node)
        for (s in this[node].orEmpty()) {
            if (result.add(s)) {
                closedSuccTo(result, s, includeNode)
            }
        }
        return result
    }

    fun Map<Char, Set<Char>>.closedSucc(node: Char, includeNode: Boolean): Set<Char> =
        closedSuccTo(mutableSetOf<Char>(), node, includeNode)

    fun assertSetEquals(value: Set<Char>, comparand: Set<Char>, context: String) {
        assertEquals(value.isEmpty(), comparand.isEmpty(), context)
        assertEquals(value.size, comparand.size, context)
        for (c in 'a'..'z') {
            assertEquals(value.contains(c), comparand.contains(c), context)
        }
        assertEquals(value, comparand, context)
    }

    private fun simpleTest(graph: Map<Char, Set<Char>>) {
        val closures = transitiveClosure(graph)
        val reflexive = transitiveClosure(graph, reflexive = true)

        val allNodes = graph.keys + graph.flatMap { it.value }
        for (node in allNodes) {
            assertEquals(graph.closedSucc(node, false), closures[node]!!, node.toString())
            assertEquals(graph.closedSucc(node, true), reflexive[node]!!, node.toString())
        }
    }

    private fun treeTest(graph : MultiMap<Char, Char>) {
        val allNodes = graph.keys + graph.flatMap { it.value }
        val parent = mutableMapOf<Char, Char>().apply {
            graph.pairs.forEach { (k, v) ->
                check(v !in keys) { "Supposed to be a tree" }
                put(v, k)
            }
        }
        val closures = TreeTransitiveClosure(parent)
        for (node in allNodes) {
            val c = allNodes.filterTo(mutableSetOf()) { closures.isAncestor(node, it) }
            assertEquals(graph.closedSucc(node, true), c, node.toString())
        }
    }

    @Test
    fun simpleTree() {
        val tree = mapOf(
            'a' to setOf('b', 'c'),
            'b' to setOf('d', 'e', 'f'),
            'c' to setOf('g'),
            'e' to setOf('h', 'i', 'j'),
            'g' to setOf('k', 'l'),
            'k' to setOf('m')
        )
        simpleTest(tree)
        treeTest(tree)
    }

    @Test
    fun twoSimpleTrees() {
        simpleTest(
            mapOf(
                'a' to setOf('b', 'c'),
                'b' to setOf('d', 'e', 'f'),
                'c' to setOf('g'),
                'e' to setOf('h', 'i', 'j'),
                'k' to setOf('l', 'm'),
                'm' to setOf('n')
            )
        )
    }

    @Test
    fun simpleDAG() {
        simpleTest(
            mapOf(
                'a' to setOf('b', 'c'),
                'b' to setOf('d', 'e', 'g'),
                'c' to setOf('g'),
                'e' to setOf('h', 'i', 'j')
            )
        )
    }

    @Test
    fun simpleDG() {
        simpleTest(
            mapOf(
                'a' to setOf('b', 'c'),
                'b' to setOf('d', 'e', 'g'),
                'c' to setOf('g'),
                'e' to setOf('h', 'i', 'b')
            )
        )
    }
}
