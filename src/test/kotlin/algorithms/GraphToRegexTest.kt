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

import datastructures.*
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

class GraphToRegexTest {
    private val n1 = "n1"
    private val n2 = "n2"
    private val n3 = "n3"
    private val n4 = "n4"
    private val n5 = "n5"
    private val n6 = "n6"
    private val n7 = "n7"

    private val l1 = "l1"
    private val l2 = "l2"
    private val l3 = "l3"
    private val l4 = "l4"
    private val l5 = "l5"
    private val l6 = "l6"
    private val l7 = "l7"

    @Test
    fun test01() {
        val relation = mutableMultiMapOf<String, String>()
        relation.add(n1, n2)
        relation.add(n2, n3)

        val labelMapping = HashMap<Pair<String, String>, String>()
        labelMapping[n1 to n2] = l1
        labelMapping[n2 to n3] = l2

        val lGraph = LabelledGraphWithSourceAndSink(
            LabelledGraph(
                relation,
                labelMapping
            ), n1, n3
        )
        val regex =
            labelledGraphToRegex(
                lGraph,
                associativityRequirement = AssociativityRequirement.FORCE_TIMES_RIGHTASSOCIATIVE
            )

        println()
        println("$lGraph")
        println()
        println("$regex")

        val nfa = RegexToNFA(regex, StringStateFactory()).result

        assertTrue { nfa.accepts(Word(l1, l2)) }
        assertFalse { nfa.accepts(Word(l1, l3)) }
        assertFalse { nfa.accepts(Word()) }
    }

    inner class StringStateFactory : StateFactory<String> {
        var ctr = 0
        override fun freshState(): String = "state${ctr++}"
    }

    @Test
    fun test02() {
        val graph = MutableLabelledGraph<String, String>()
        graph.put(n1, l1, n2)
        graph.put(n1, l2, n3)
        graph.put(n2, l3, n4)
        graph.put(n3, l4, n4)
        graph.put(n4, l5, n5)

        val lgwss = LabelledGraphWithSourceAndSink(graph.freeze(), n1, n5)
        val regex =
            labelledGraphToRegex(
                lgwss,
                associativityRequirement = AssociativityRequirement.FORCE_TIMES_RIGHTASSOCIATIVE
            )

        println()
        println("$lgwss")
        println()
        println("$regex")

        val nfa = RegexToNFA(regex, StringStateFactory()).result

        assertTrue { nfa.accepts(Word(l1, l3, l5)) }
        assertTrue { nfa.accepts(Word(l2, l4, l5)) }
        assertFalse { nfa.accepts(Word(l1, l2, l5)) }
        assertFalse { nfa.accepts(Word(l3, l3, l5)) }
        assertFalse { nfa.accepts(Word()) }
        assertFalse { nfa.accepts(Word(l5, l1, l2)) }
    }

    @Test
    fun test02a() {
        val graph = MutableLabelledGraph<String, String>()
        graph.put(n1, l1, n2)
        graph.put(n1, l2, n3)
        graph.put(n2, l3, n4)
        graph.put(n3, l4, n4)
        graph.put(n4, l5, n5)
        graph.put(n5, l6, n6)

        val lGraph = LabelledGraphWithSourceAndSink(graph.freeze(), n1, n6)

        val regex =
            labelledGraphToRegex(
                lGraph,
                associativityRequirement = AssociativityRequirement.FORCE_TIMES_RIGHTASSOCIATIVE
            )

        println()
        println("$lGraph")
        println()
        println("$regex")

        val nfa = RegexToNFA(regex, StringStateFactory()).result

        assertTrue { nfa.accepts(Word(l1, l3, l5, l6)) }
        assertTrue { nfa.accepts(Word(l2, l4, l5, l6)) }
        assertFalse { nfa.accepts(Word(l1, l2, l5, l6)) }
        assertFalse { nfa.accepts(Word(l3, l3, l5)) }
        assertFalse { nfa.accepts(Word()) }
        assertFalse { nfa.accepts(Word(l5, l1, l2)) }
    }

    @Test
    fun test03() {
        val graph = MutableLabelledGraph<String, String>()
        graph[n1 to n2] = l1
        graph[n1 to n3] = l2
        graph[n2 to n4] = l3
        graph[n4 to n5] = l5

        val lGraph = LabelledGraphWithSourceAndSink(graph.freeze(), n1, n5)
        val regex =
            labelledGraphToRegex(
                lGraph,
                associativityRequirement = AssociativityRequirement.FORCE_TIMES_RIGHTASSOCIATIVE
            )

        println()
        println("$lGraph")
        println()
        println("$regex")

        val nfa = RegexToNFA(regex, StringStateFactory()).result

        assertTrue { nfa.accepts(Word(l1, l3, l5)) }
        assertFalse { nfa.accepts(Word(l2, l4, l5)) }
        assertFalse { nfa.accepts(Word(l1, l2, l5)) }
        assertFalse { nfa.accepts(Word(l3, l3, l5)) }
        assertFalse { nfa.accepts(Word()) }
        assertFalse { nfa.accepts(Word(l5, l1, l2)) }
    }

    @Test
    fun test04() {
        val graph = MutableLabelledGraph<String, String>()
        graph[n1 to n2] = l1
        graph[n1 to n3] = l2
        graph[n2 to n4] = l3
        graph[n4 to n5] = l5
        graph[n5 to n6] = l6

        val lGraph = LabelledGraphWithSourceAndSink(graph.freeze(), n1, n6)
        val regex =
            labelledGraphToRegex(
                lGraph,
                associativityRequirement = AssociativityRequirement.FORCE_TIMES_RIGHTASSOCIATIVE
            )

        println()
        println("$lGraph")
        println()
        println("$regex")

        val nfa = RegexToNFA(regex, StringStateFactory()).result

        assertTrue { nfa.accepts(Word(l1, l3, l5, l6)) }
        assertFalse { nfa.accepts(Word(l2, l4, l5, l6)) }
        assertFalse { nfa.accepts(Word(l1, l2, l5)) }
        assertFalse { nfa.accepts(Word(l3, l3, l5)) }
        assertFalse { nfa.accepts(Word()) }
        assertFalse { nfa.accepts(Word(l5, l1, l2)) }
    }
}
