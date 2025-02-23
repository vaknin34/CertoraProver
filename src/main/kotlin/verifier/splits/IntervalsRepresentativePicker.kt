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

import analysis.opt.intervals.ExtBig
import analysis.opt.intervals.Interval
import analysis.opt.intervals.Intervals
import datastructures.stdcollections.*
import utils.*
import java.math.BigInteger


object IntervalsRepresentativePicker {

    /**
     * Pick [howMany] samples from `this` in a hopefully spread out manner.
     * If there are less than [howMany] points in [this], then only the points in this are returned.
     */
    private fun Interval.NonEmpty.pickRepresentatives(howMany: Int): Set<BigInteger> {
        if (numElements.nOrNull()?.toIntOrNull()?.let { it <= howMany } == true) {
            return valSequence.toSet()
        }
        return buildSet {
            low.nOrNull()?.let(::add)
            high.nOrNull()?.let(::add)
            var current = BigInteger.ONE
            when {
                low == ExtBig.MInf && high == ExtBig.Inf -> {
                    while (size < howMany) {
                        add(current)
                        current = -(current * 2)
                    }
                }

                low == ExtBig.MInf -> {
                    while (size < howMany) {
                        add(high.n - current)
                        current *= 2
                    }
                }

                high == ExtBig.Inf -> {
                    while (size < howMany) {
                        add(low.n + current)
                        current *= 2
                    }
                }

                else -> {
                    if (size < howMany && 0 in this@pickRepresentatives) {
                        add(BigInteger.ZERO)
                    }
                    if (size < howMany) {
                        add((low.n + high.n) / 2)
                    }
                    while (size < howMany) {
                        add(low.n + current)
                        if (size < howMany) {
                            add(high.n - current)
                        }
                        current++
                    }
                }
            }

        }
    }


    /** Pick [howMany] samples from [intervals] in a hopefully spread out manner */
    fun pickRepresentatives(intervals: Intervals, howMany: Int) =
        buildSet {
            // start with shorter intervals, and always round up. That should make it fine.
            intervals.sortedBy { it.numElements }.forEachIndexed { i, interval ->
                if (size < howMany) {
                    addAll(
                        interval.pickRepresentatives(
                            // (amount of reps that remain to pick) / (how many intervals remain to pick from)
                            (howMany - size).divRoundUp(intervals.size - i)
                        )
                    )
                }
            }
        }

}

