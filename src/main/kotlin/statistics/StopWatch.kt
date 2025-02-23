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

package statistics

/** Something that takes the time between the [start] and the [stop] call. */
interface StopWatch {
    fun start()
    fun stop()
    fun timeRecordsOf(vararg moreKeys: SDFeatureKey): AggregatedElapsedTimeStats
}

/**
 * Viewing a [ElapsedTimeStats] together with a [TimeTag] as a [StopWatch].
 */
class MilliTimeElapserStopWatch(
    private val elapser: ElapsedTimeStats,
    private val tag: TimeTag,
    private val timeViews: MutableList<SDElement<Long>> = mutableListOf()
) : StopWatch {

    override fun start() {
        elapser.startMeasuringTimeOf(tag)
    }

    override fun stop() {
        timeViews.add(elapser.endMeasuringTimeOf(tag))
    }

    override fun timeRecordsOf(vararg moreKeys: SDFeatureKey) =
        AggregatedElapsedTimeStats(
            extractedData = timeViews.deepCopy(),
            precedingKeys = elapser.precedingKeys + moreKeys
        )
}
