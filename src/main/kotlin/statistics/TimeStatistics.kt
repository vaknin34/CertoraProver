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

import kotlin.time.TimedValue
import kotlin.time.measureTimedValue

typealias TimeTag = StatsTag

fun String.toTimeTag() = TimeTag(this)

/******************************* Time Statistical Features (TimeStats) ************************/
data class TimeStampStats(
    override val precedingKeys: List<SDFeatureKey> = listOf(),
    override val extractedData: MutableList<SDElement<Long>> = mutableListOf(),
) : SDFeature<Long> {
    constructor(vararg _precedingKeys: SDFeatureKey) : this(precedingKeys = _precedingKeys.toList())

    fun stampCurrentTime(tag: TimeTag) = apply {
        extractedData.add(SDElement(tag, System.currentTimeMillis()))
    }

    override val descriptor = SDDescriptor.DateTimeStringDescriptor
    override fun fork(vararg moreKeys: SDFeatureKey): TimeStampStats =
        copy(extractedData = extractedData.deepCopy(), precedingKeys = precedingKeys + moreKeys)
}

data class TimedResult<T>(val result: T, val time: Long)

data class ElapsedTimeStats(
    override val precedingKeys: List<SDFeatureKey> = listOf(),
    override val extractedData: MutableList<SDElement<Long>> = mutableListOf(),
    private val tagToStartTimeStamp: MutableMap<TimeTag, Long> = mutableMapOf(),
    private val globalStartTimeStamp: Long = System.currentTimeMillis(),
) :
    SDFeature<Long> {
    constructor(vararg _precedingKeys: SDFeatureKey) : this(
        precedingKeys = _precedingKeys.toList()
    )

    fun <T> measure(t: String, f: () -> T): TimedValue<T> {
        val tag = t.toTimeTag()
        return measureTimedValue {
            f()
        }.also {
            extractedData.add(SDElement(tag, it.duration.inWholeMilliseconds))
        }
    }

    fun startMeasuringTimeOf(tag: TimeTag) = apply { tagToStartTimeStamp[tag] = System.currentTimeMillis() }


    fun endMeasuringTimeOf(tag: TimeTag): SDElement<Long> {
        val tagElapsedMillSec = System.currentTimeMillis() - tagToStartTimeStamp.getOrDefault(tag, globalStartTimeStamp)
        val element = SDElement(tag, tagElapsedMillSec)
        extractedData.add(element)
        return element
    }

    fun <T> measure(tag : TimeTag, f : () -> T) : T {
        startMeasuringTimeOf(tag)
        val result = f()
        endMeasuringTimeOf(tag)
        return result
    }

    fun takeLastTimeRecords(n: Int, vararg moreKeys: SDFeatureKey) = ElapsedTimeStats(
        precedingKeys = precedingKeys + moreKeys.toList(),
        extractedData = extractedData.takeLast(n).toMutableList(),
    )

    override fun describeData(): Map<String, List<Long>> = descriptor.describeData(extractedData)

    override val descriptor = SimpleTimeDescriptor()
    override fun fork(vararg moreKeys: SDFeatureKey): ElapsedTimeStats =
        copy(extractedData = extractedData.deepCopy(), precedingKeys = precedingKeys + moreKeys)
}


data class AggregatedElapsedTimeStats(
    override val precedingKeys: List<SDFeatureKey>,
    override val extractedData: MutableList<SDElement<Long>>,
) : SDFeature<Long> {
    constructor(
        elapsedTimeStats: ElapsedTimeStats,
        vararg moreKeys: SDFeatureKey,
    ) : this(elapsedTimeStats.precedingKeys + moreKeys, elapsedTimeStats.extractedData.deepCopy())

    override val descriptor = SDDescriptor.AggregatedDescriptor

    override fun describeData(): Map<String, Long> = descriptor.describeData(extractedData)

    override fun fork(vararg moreKeys: SDFeatureKey): AggregatedElapsedTimeStats =
        copy(extractedData = extractedData.deepCopy(), precedingKeys = precedingKeys + moreKeys)
}
