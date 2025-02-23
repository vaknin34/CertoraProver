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

import datastructures.NFA
import java.lang.UnsupportedOperationException

/**
 * Compute a nondeterministic finite automaton (NFA) from a [Regex].
 * Mostly naive implementation of Thompson's construction [https://en.wikipedia.org/wiki/Thompson%27s_construction].
 *
 * @param L letter type of the regex and NFA
 */
class RegexToNFA<S, L>(private val inputRegex: Regex<L>, private val stateFactory: StateFactory<S>) {

    val result = process(inputRegex, stateFactory.freshState(), stateFactory.freshState())

    private fun process(regex: Regex<L>, source: S, sink: S): NFA<S, L> {
        val res = when (regex) {
            is Regex.Empty -> throw UnsupportedOperationException("TODO process $regex $source $sink")
            is Regex.LetterOrEpsilon.Epsilon -> NFA.epsilon(source, sink)
            is Regex.LetterOrEpsilon.Letter -> NFA.singleLetter(source, regex.letter, sink)
            is Regex.Plus ->
                stateFactory.freshState().let { sink1 ->
                    stateFactory.freshState().let { source1 ->
                        NFA.plus(
                            regex.ops.map { process(it, source1, sink1) },
                            source,
                            sink
                        )
                    }

                }
            is Regex.Times -> {
                check(regex.ops.size > 1)

                var prevState = stateFactory.freshState()
                var currNFA = process(regex.ops[0], source, prevState)

                for (i in regex.ops.indices) {
                    if (i == 0) {
                        // first operand was already processed outside of loop
                        continue
                    }
                    val currRegex = regex.ops[i]
                    val currState = if (i == regex.ops.size - 1) sink else stateFactory.freshState()
                    check(currNFA.accepting == prevState)
                    currNFA = NFA.times(currNFA, process(currRegex, prevState, currState))
                    // operations done update prev-variables
                    prevState = currState
                }
                currNFA
            }
            is Regex.Star -> throw UnsupportedOperationException("TODO process $regex $source $sink")
        }
        check(res.initial == source)
        check(res.accepting == sink)
        return res
    }
}

interface StateFactory<S> {
    fun freshState(): S
}

interface LetterFactory<L> {
    fun freshLetter(): L
}