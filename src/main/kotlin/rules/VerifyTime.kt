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

package rules

import kotlin.math.min
import kotlin.math.max

/**
 * The time it took to verify a rule.
 */
sealed class VerifyTime {

    /** The time in seconds it took to verify a rule. */
    abstract val timeSeconds: Long

    /**
     * Time-interval, verification started at [startTime]
     * and terminated at [endTime].
     */
    data class WithInterval(
        val startTime: Long,
        val endTime: Long
    ) : VerifyTime() {

        init {
            require(startTime <= endTime) { "Expected the startTime $startTime to be at most the endTime $endTime" }
        }

        override val timeSeconds: Long
            get() = (endTime - startTime) / 1000
    }

    /** No time is computed. */
    object None : VerifyTime() {
        override val timeSeconds: Long
            get() = 0
    }

    infix fun join(other: VerifyTime): VerifyTime {
        return when {
            this == None && other == None -> {
                // nothing smarter to have here
                None
            }

            this is WithInterval && other == None -> {
                // we take the time-interval
                this
            }

            this == None && other is WithInterval -> {
                // we take the time-interval
                other
            }

            this is WithInterval && other is WithInterval -> {
                // a join over the intervals
                WithInterval(
                    startTime = min(this.startTime, other.startTime),
                    endTime = max(this.endTime, other.endTime)
                )
            }

            else -> throw IllegalStateException("Should be unreachable (inside VerifyTime.join())")
        }
    }
}

data class ResultAndTime<T>(
    val result: T,
    val verifyTime: VerifyTime
)
