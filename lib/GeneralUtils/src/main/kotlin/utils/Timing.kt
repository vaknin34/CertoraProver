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

package utils

import kotlinx.serialization.Serializable
import kotlin.time.Duration
import kotlin.time.TimeMark
import kotlin.time.TimeSource

/**
 * Get current time as a [TimeMark]. This can be used as a starting point to
 * measure a time from hereon via [TimeMark.elapsedNow]. Consider using
 * [TimeSource.measureTimedValue] instead.
 */
fun getCurrentTime(): TimeMark = TimeSource.Monotonic.markNow()

/**
 * A convenience class to store "absolute" points in time. Those almost always
 * don't mean anything in our case, instead we consider the time since the
 * process started (as a [Duration]).
 * For convenience, we implement [elapsedNow] to return the time elapsed since
 * the stored "absolute" point in time.
 */
@JvmInline
@Serializable
value class TimeSinceStart(val d: Duration): java.io.Serializable {
    companion object {
        /** The epoch of our time points: the start of the process */
        val epoch: TimeMark = getCurrentTime()
        /** Create an object with the current time */
        operator fun invoke() = TimeSinceStart(epoch.elapsedNow())
    }
    /** Obtain the duration elapsed between [this] point in time and now. */
    fun elapsedNow(): Duration = (epoch + d).elapsedNow()
    /** Render wrapped [Duration] as an ISO duration string. */
    override fun toString(): String = d.toIsoString()
}
