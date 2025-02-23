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

import datastructures.stdcollections.filter
import kotlin.time.measureTimedValue
import kotlin.time.TimedValue
import kotlinx.serialization.builtins.MapSerializer
import kotlinx.serialization.json.Json
import kotlinx.serialization.json.JsonElement
import kotlinx.serialization.json.JsonObject
import kotlinx.serialization.json.JsonTransformingSerializer
import kotlinx.serialization.KSerializer
import java.io.Serializable

@kotlinx.serialization.Serializable
sealed class StatsValue : utils.HasKSerializable {
    @kotlinx.serialization.Serializable
    data class Ms(val time: Long) : StatsValue() {
        companion object {
            operator fun <T> invoke(t: TimedValue<T>) = Ms(t.duration.inWholeMilliseconds)
        }
    }

    @kotlinx.serialization.Serializable
    data class Bool(val value: Boolean) : StatsValue()

    @kotlinx.serialization.Serializable
    data class Str(val value: String) : StatsValue()


    @kotlinx.serialization.Serializable
    data class Count(val value: Int) : StatsValue()

    /**
     *  Unwraps a [StatsValue] to its inner primitive type
     **/
    object Serializer : JsonTransformingSerializer<StatsValue>(serializer()) {
        override fun transformSerialize(element: JsonElement): JsonElement =
            (element as? JsonObject)?.entries?.firstOrNull { it.key != "type" }?.value ?: element
    }
}

abstract class IStatsJson<K> : Serializable {
    abstract val stats: MutableMap<K, StatsValue>
    abstract val keySerializer: KSerializer<K>
    abstract val collectKey: String
    open val totalMsKey: K? = null

    override fun toString(): String =
        format.encodeToString(MapSerializer(keySerializer, StatsValue.Serializer), stats)


    fun put(key: K, value: StatsValue) {
        stats[key] = value
    }

    inline fun <T> measure(key: K, f: () -> T): T {
        val (result, _) = measureTimedValue(f).also {
            stats[key] = StatsValue.Ms(it)
        }
        return result
    }

    companion object {
        val format = Json { prettyPrint = true }
        fun <K, T : IStatsJson<K>> T.totalMs(): T = apply {
            totalMsKey?.let { key ->
                stats[key] =
                    stats.filter { it.key != key }.mapNotNull { (it.value as? StatsValue.Ms)?.time }
                        .sum()
                        .let(StatsValue::Ms)

            }
        }

        fun <K, T : IStatsJson<K>> T.merge(other: T): T = apply {
            stats.putAll(other.stats)
        }

        fun <K, T : IStatsJson<K>> T.collect(vararg prefixes: SDFeatureKey) =
            SDCollectorFactory.collector().collectFeature(
                GeneralKeyValueStats<T>(prefixes.toList()).addKeyValue(
                    collectKey,
                    this
                )
            )
    }
}
