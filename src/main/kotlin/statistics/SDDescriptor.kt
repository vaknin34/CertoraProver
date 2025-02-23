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

import datastructures.stdcollections.*
import java.time.Instant
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter
import java.util.*

/**
 * Creates a description of the raw stats data extracted by the specified [SDDescriptor.extractor].
 */
sealed class SDDescriptor<P> {
    abstract fun describeData(data: List<SDElement<P>>): Map<String, Any>

    class ScalarDescriptor<P> : SDDescriptor<P>() {
        override fun describeData(data: List<SDElement<P>>) = data.groupByKey { it }.mapValues { it.value.singleOrNull() ?: it.value }
    }

    class IdDescriptor<P> : SDDescriptor<P>() {
        override fun describeData(data: List<SDElement<P>>) = data.groupByKey { it }
    }

    object DateTimeStringDescriptor : SDDescriptor<Long>() {
        override fun describeData(data: List<SDElement<Long>>) = data.groupByKey(::milliTimeStampStringer)

        private fun milliTimeStampStringer(milliStamp: Long): String {
            return LocalDateTime.ofInstant(
                Instant.ofEpochMilli(milliStamp), TimeZone.getDefault().toZoneId()
            ).format(DateTimeFormatter.ofPattern("MM/dd/yyyy HH:mm:ss"))
        }
    }

    object AggregatedDescriptor : SDDescriptor<Long>() {
        override fun describeData(data: List<SDElement<Long>>) =
            data.groupingBy { it.key }.fold(0L) { sum, element -> sum + element.statsData }
    }
}
typealias SimpleTimeDescriptor = SDDescriptor.IdDescriptor<Long>

private inline fun <P, R> List<SDElement<P>>.groupByKey(
    statDataMapper: (P) -> R,
): Map<String, List<R>> {
    val grouped: Map<String, MutableList<R>> = groupingBy { it.key }.aggregate { _, acc, element, _ ->
        val data = statDataMapper(element.statsData)
        acc?.apply { add(data) } ?: mutableListOf(data)
    }
    return grouped
}
