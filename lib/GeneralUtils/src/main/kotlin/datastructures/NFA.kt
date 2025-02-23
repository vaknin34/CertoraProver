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

import utils.*

/**
 * @param S state type
 * @param L letter type
 * @param graph graph underlying the NFA, note that edge label type is [LetterOrEpsilon<L>] -- LetterOrEpsilon.Epsilon() represents an epsilon transition
 *
 * Note: to have a really nice implementation of NFAs, we might want
 *   - sets of initial and accepting states
 *   - an explicit alphabet
 *   - standard operations (intersection, emptiness, etc)
 *   - more..
 */
class NFA<S, L>(private val graph: LabelledGraph<S, LetterOrEpsilon<L>>, val initial: S, val accepting: S) {

    sealed class LetterOrEpsilon<L> {
        @Suppress("UNCHECKED_CAST")
        class Epsilon<L> private constructor() : LetterOrEpsilon<L>() {
            override fun toString(): String = utils.epsilon

            companion object {
                /** see [algorithms.Regex.Empty.invoke] for thoughts on this solution */
                private val instance = Epsilon<Any>()
                operator fun <L> invoke(): Epsilon<L> = instance as Epsilon<L>
            }
        }

        data class Letter<L>(val letter: L) : LetterOrEpsilon<L>()
    }

    fun accepts(word: Word<L>): Boolean {
        var currentStates = setOf(initial)
        // using this to make switch to more than one accepting state easier
        val acceptingStates = setOf(accepting)

        var currentLetterIndex = 0

        while (true) {
            if (currentLetterIndex > word.size) break
            if (currentStates.isEmpty()) break
            if (currentLetterIndex == word.size) return currentStates.containsAny(acceptingStates)
            currentStates = currentStates.flatMap { getSuccessors(it, word[currentLetterIndex]) }.toSet()
            currentLetterIndex++
        }
        return false
    }

    private fun getSuccessors(state: S, letter: L): Set<S> {
        return getEpsilonSuccessors(state)
            .flatMap { getDirectSuccessors(it, LetterOrEpsilon.Letter(letter)) }.toSet()
            .flatMap { getEpsilonSuccessors(it) }.toSet()
    }

    /**
     * @param letter a letter or LetterOrEpsilon.Epsilon(), which designates epsilon
     */
    private fun getDirectSuccessors(state: S, letter: LetterOrEpsilon<L>): Set<S> =
        graph.succs(state).filter { succ -> graph.getEdgeLabel(state, succ) == letter }.toSet()

    /**
     * get all states that can be reach through 0 or more epsilon transitions from [state]
     */
    private fun getEpsilonSuccessors(state: S): Set<S> {
        val res = mutableSetOf(state)
        while (true) {
            val new = res.flatMap {
                getDirectSuccessors(
                    it,
                    LetterOrEpsilon.Epsilon()
                )
            }.toSet()
            if (res.containsAll(new)) {
                // reached fixpoint
                return res
            }
            res.addAll(new)
        }
    }

    companion object {

        fun <S, L> singleLetter(source: S, letter: L, sink: S) =
            NFA<S, L>(
                LabelledGraph.singleEdge(
                    source,
                    LetterOrEpsilon.Letter(letter),
                    sink
                ), source, sink
            )

        fun <S, L> epsilon(source: S, sink: S) =
            NFA<S, L>(
                LabelledGraph.singleEdge(
                    source,
                    LetterOrEpsilon.Epsilon(),
                    sink
                ), source, sink
            )

        fun <S, L> plus(ops: List<NFA<S, L>>, newInit: S, newAccepting: S): NFA<S, L> {
            val newLg = MutableLabelledGraph<S, LetterOrEpsilon<L>>()

            ops.forEach {
                it.graph.allEdges.forEach { (n1, n2) -> newLg.put(n1, it.graph.getEdgeLabel(n1, n2), n2) }
            }
//            op1.graph.allEdges.forEach { (n1, n2) -> newLg.put(n1, op1.graph.getEdgeLabel(n1, n2), n2) }
//            op2.graph.allEdges.forEach { (n1, n2) -> newLg.put(n1, op2.graph.getEdgeLabel(n1, n2), n2) }

            ops.forEach {
                newLg.put(newInit, LetterOrEpsilon.Epsilon(), it.initial)
                newLg.put(it.accepting, LetterOrEpsilon.Epsilon(), newAccepting)
            }
//            newLg.put(newInit, LetterOrEpsilon.Epsilon(), op1.initial)
//            newLg.put(newInit, LetterOrEpsilon.Epsilon(), op2.initial)
//            newLg.put(op1.accepting, LetterOrEpsilon.Epsilon(), newAccepting)
//            newLg.put(op2.accepting, LetterOrEpsilon.Epsilon(), newAccepting)

            return NFA(newLg.freeze(), newInit, newAccepting)
        }

        fun <S, L> times(op1: NFA<S, L>, op2: NFA<S, L>): NFA<S, L> {
            check(op1.accepting == op2.initial)
            { "should not happen" }
            val newLg =
                MutableLabelledGraph<S, LetterOrEpsilon<L>>()
            op1.graph.allEdges.forEach { (n1, n2) -> newLg.put(n1, op1.graph.getEdgeLabel(n1, n2), n2) }
            op2.graph.allEdges.forEach { (n1, n2) -> newLg.put(n1, op2.graph.getEdgeLabel(n1, n2), n2) }
            return NFA(newLg.freeze(), op1.initial, op2.accepting)
        }
    }
}

data class Word<L>(val list: List<L>) : List<L> by list {
    constructor(vararg letters: L) : this(letters.toList())
}
