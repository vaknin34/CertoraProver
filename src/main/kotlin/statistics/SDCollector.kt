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

import config.Config
import json.BasicJsonifier
import log.ArtifactManagerFactory
import log.Logger
import log.LoggerTypes
import utils.*


@Suppress("unused")
private val logger = Logger(LoggerTypes.COMMON)

interface SDCollector {
    /**
     * Adds the specified statistical [feature]. If [SDFeature.hasPrecedingKeys], then
     * its data keys become the innermost keys and [SDFeature.precedingKeys] become the preceding keys of [feature].
     * If a mapping from the key or an inner key already exists, then the values are merged.
     */
    fun collectFeature(feature: SDFeature<*>)

    /**
     * Adds the data of the specified [RunID].
     */
    fun collectRunId(runId: RunID = RunIDFactory.runId()): SDCollector

    /**
     * outputs the stats as a json string
     */
    fun getAsString(): String

    /**
     * Outputs the stats to a json file.
     */
    fun toFile(statsDataFile: String = Config.getJSONStatsDataOutputFile())

    fun read(key: FullyQualifiedSDFeatureKey): SDFeature<*>?
}


object SDCollectorFactory {
    private val collector by lazy {
        if (Config.EnableStatistics.get() && ArtifactManagerFactory.isEnabled()) {
            EnabledSDCollector()
        } else {
            DisabledSDCollector
        }
    }

    private val splitStatsCollector by lazy {
        if (Config.EnableStatistics.get() && ArtifactManagerFactory.isEnabled()) {
            EnabledSDCollector()
        } else {
            DisabledSDCollector
        }
    }

    fun collector(): SDCollector = collector
    fun splitStatsCollector(): SDCollector = splitStatsCollector
}

/**
 * Collects stats data provided by [SDFeature]s.
 */
data class EnabledSDCollector(private val collectedData: MutableMap<FullyQualifiedSDFeatureKey, SDFeature<*>> = mutableMapOf()) :
    SDCollector {

    override fun read(key: FullyQualifiedSDFeatureKey): SDFeature<*>? = collectedData[key]

    private fun<T> access(f: MutableMap<FullyQualifiedSDFeatureKey, SDFeature<*>>.() -> T): T =
        synchronized(this) { collectedData.f() }

    override fun collectFeature(feature: SDFeature<*>) {
        val key = feature.fullFeatureKey()
        access { compute(key) { _, value -> value?.unsafeMerge(feature) ?: feature.fork() } }
    }

    override fun collectRunId(runId: RunID) = apply {
        runId.allData.forEach { collectFeature(it) }
    }

    override fun getAsString(): String {
        val features = access { values.mapTo(mutableListOf()) { f -> f.feature } }

        val data = features.fold(emptyMap(), ::getMergedMaps)

        return BasicJsonifier.mapToJson(data)
    }

    override fun toFile(statsDataFile: String) {
        val jsonString = getAsString()

        ArtifactFileUtils.getWriterForFile(statsDataFile, overwrite = true).use {
            it.write(jsonString)
        }
    }

    companion object {
        /**
         * merge values of stats collector - to a tree to serialize to json
         * where [accum] is the current value, and [value] is newly gathered one
         **/
        private fun getMergedMaps(accum: Map<String, Any>, value: Map<String, Any>): Map<String, Any> {
            val mergedMap = (value - accum.keys) + (accum - value.keys)
            val intersection = value.keys.intersect(accum.keys)
            return intersection.associateWithTo(mergedMap.toSortedMap()) { getMergedValues(accum[it], value[it]) }
        }

        /**
         * merge values of stats collector - to a tree to serialize to json
         * where [accum] is the current value, and [value] is newly gathered one
         **/
        private fun getMergedValues(accum: Any?, value: Any?): Any = if (accum is Map<*, *> && value is Map<*, *>) {
            // we know that map keys are strings so this is efficient
            val mergedMap = (value - accum.keys).plus(accum - value.keys)
                .toSortedMap { a, b -> a.toString().compareTo(b.toString()) }
            val intersection = value.keys.intersect(accum.keys)
            intersection.associateWithTo(mergedMap) { getMergedValues(accum[it], value[it]) }
        } else if (accum is List<*> && value is Map<*, *>) {
            // if the accum value is a list - a nested map should be in it
            val (maps, rest) = accum.partition { it is Map<*, *> }
            check(maps.size <= 1) { "there should be only one map in each level by construction, but $accum has more" }
            val map =
                maps.firstOrNull()?.let { getMergedValues(it, value) } ?: value
            rest + listOf(map)
        } else {
            val output = asList(accum) + asList(value)
            // singleton values should not be wrapped with a `list`
            output.singleOrNull() ?: output
        }

        private fun asList(v: Any?): List<*> = when (v) {
            is List<*> -> v
            is Set<*> -> v.toList()
            else -> listOfNotNull(v)
        }
    }
}

object DisabledSDCollector : SDCollector {
    override fun collectFeature(feature: SDFeature<*>) = Unit
    override fun collectRunId(runId: RunID) = this

    override fun getAsString(): String = ""
    override fun toFile(statsDataFile: String) {}

    override fun read(key: FullyQualifiedSDFeatureKey): SDFeature<*>? = null
}
