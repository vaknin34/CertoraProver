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

import utils.uncheckedAs
import java.io.Serializable

interface SDFeature<P> {
    /**
     * Specifies the keys that should appear before [descriptor]'s key-value pairs in the generated JSON stats file.
     * The keys would appear in the JSON file in accordance with their order of occurrence in [precedingKeys], i.e.,
     * the first (resp. last) element would be the outermost (resp. innermost) key.
     * Note that two distinct [SDFeature]s may have the same preceding keys.
     * If no keys are specified, the [descriptor]'s keys would appear at the outermost level in the generated JSON stats file.
     */
    val precedingKeys: List<SDFeatureKey>

    val extractedData: MutableList<SDElement<P>>

    /**
     * The underlying [SDDescriptor] of this feature.
     */
    val descriptor: SDDescriptor<P>

    fun describeData() = descriptor.describeData(extractedData)

    /**
     * Should be invoked by an [SDCollector]. Returns the stats data of this [SDFeature].
     *
     * @see SDCollector
     */
    val feature: Map<String, Any>
        get() = precedingKeys.reversed().fold(describeData()) { accum, key -> mapOf(key.keyAsString to accum) }


    fun hasPrecedingKeys() = precedingKeys.isNotEmpty()

    fun hasData() = extractedData.isNotEmpty()

    fun fork(vararg moreKeys: SDFeatureKey): SDFeature<P>

    /**
     * Given [other] [SDFeature] merge its collected statistics to this
     *
     * It is not guaranteed that the internal state of [other] is merged into this
     * for example: [ElapsedTimeStats].tagToStartTimeStamp is not merged
     *
     * assumes the caller guaranteed that
     * ~~~
     * this.fullFeatureKey() == other.fullFeatureKey()
     * ~~~
     *
     * if the other [P] != this [P],
     * the operation results is undefined
     *
     * else if the other [fullFeatureKey] != [fullFeatureKey],
     * the makes no sense but will succeed silently
     **/
    fun unsafeMerge(other: SDFeature<*>) = apply { extractedData.addAll(other.extractedData.uncheckedAs()) }

    fun fullFeatureKey(): FullyQualifiedSDFeatureKey = FullyQualifiedSDFeatureKey(precedingKeys, javaClass.canonicalName)
}

data class SDFeatureKey(val keyAsString: String) {
    override fun toString(): String = keyAsString
}

/**
 * A unique identifier of [SDFeature]
 * Meant to allow safe usage of [SDFeature.unsafeMerge] where type parameters are erased
 **/
data class FullyQualifiedSDFeatureKey(val precedingKeys: List<SDFeatureKey>, val name: String) : Serializable

fun String.toSDFeatureKey() = SDFeatureKey(this)


/**
 * Stats data element
 */
data class SDElement<T>(val key: String, val statsData: T) {
    constructor(tag: StatsTag, statsData: T): this(tag.tag, statsData)
}

data class StatsTag(val tag: String): Serializable

/**
 * A utility do coping a mutable-map with the guarantee that the result is not shared with `this`
 **/
internal fun<T> MutableList<T>.deepCopy(): MutableList<T> = toMutableList()
