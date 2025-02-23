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

@file:Suppress("ImportStdCollections")
@file:OptIn(kotlin.experimental.ExperimentalTypeInference::class)
package datastructures.stdcollections

import com.certora.collect.*
import datastructures.*
import utils.*

//
// Make it easy to convert Java maps to ArrayHashMap
//
fun <K, V, M : Map<K, V>> M.toPreferredMap() =
    when (this) {
        is LinkedHashMap<*, *> -> LinkedArrayHashMap<K, V>(this as Map<K, V>)
        is HashMap<*, *> -> ArrayHashMap<K, V>(this as Map<K, V>)
        else -> this // we don't know the behavior of arbitrary map types, so leave them as is.
    }

/**
    Faster iteration than [kotlin.collections.forEach], for our Map implementations.

    This cannot be named `forEach` because Kotlin's stdlib has a `forEach` function that takes precedence over this one.
    Also, this is not inline like `forEach`, because `TreapMap.forEachEntry` is not inline.

    If you need an inline version, use [forEachEntryInline] - but note that it is not as fast as this version, when
    applied to [TreapMap]s.
 */
fun <K, V> Map<out K, V>.forEachEntry(action: (Map.Entry<K, V>) -> Unit): Unit =
    this.asTreapMapOrNull()?.forEachEntry(action) ?: this.forEachEntryInline(action)

/**
    Faster iteration than [kotlin.collections.forEach], for our Map implementations.

    Use [forEachEntry] if you don't need an inline version; it is much better optimized for [TreapMap]s.
 */
inline fun <K, V> Map<out K, V>.forEachEntryInline(action: (Map.Entry<K, V>) -> Unit): Unit {
    when (this) {
        is LinkedArrayHashMap<*, *> ->
            this.uncheckedAs<LinkedArrayHashMap<K, V>>().forEachEntry {
                k, v -> action(MapEntry(k, v))
            }
        is ArrayHashMap<*, *> ->
            this.uncheckedAs<ArrayHashMap<K, V>>().forEachEntry {
                k, v -> action(MapEntry(k, v))
            }
        is ReversibleDigraph<*> ->
            (this.forward.uncheckedAs<LinkedArrayHashMap<K, V>>()).forEachEntry {
                k, v -> action(MapEntry(k, v))
            }

        // Iterating over entries in the "built" map is faster, as it avoids looking up the values
        // separately for each entry.
        is TreapMap.Builder<*, *> ->
            this.uncheckedAs<TreapMap.Builder<K, V>>().build().forEach(action)

        else -> this.forEach(action)
    }
}

inline fun <K, V> Map<out K, V>.findEntry(crossinline predicate: (K, V) -> Boolean): Pair<K, V>? {
    forEachEntryInline { (key, value) ->
        if (predicate(key, value)) {
            return (key to value)
        }
    }
    return null
}

fun <K, V> Map<K, V>.asTreapMapOrNull(): TreapMap<K, V>? =
    (this as? TreapMap<K, V>) ?: (this as? TreapMap.Builder<K, V>)?.build()

//
// Override some of the kotlin stdlib functions to use our own optimized map implementation
//
fun <K, V> mapOf(): Map<K, V> = kotlin.collections.mapOf()

fun <K, V> mapOf(vararg pairs: Pair<K, V>): Map<K, V> =
    if (pairs.size > 0) pairs.toMap(LinkedArrayHashMap(pairs.size)) else mapOf()

fun <K, V> mutableMapOf(): MutableMap<K, V> = LinkedArrayHashMap()
fun <K, V> mutableUnorderedMapOf(): MutableMap<K, V> = ArrayHashMap()

fun <K, V> mutableMapOf(vararg pairs: Pair<K, V>): MutableMap<K, V> =
    LinkedArrayHashMap<K, V>(pairs.size).apply { putAll(pairs) }
fun <K, V> mutableUnorderedMapOf(vararg pairs: Pair<K, V>): MutableMap<K, V> =
    ArrayHashMap<K, V>(pairs.size).apply { putAll(pairs) }

inline fun <K, V, R> Map<out K, V>.mapValues(transform: (Map.Entry<K, V>) -> R): Map<K, R> =
    mapValuesTo(LinkedArrayHashMap<K, R>(size), transform)

inline fun <K, V, R> Map<out K, V>.mapKeys(transform: (Map.Entry<K, V>) -> R): Map<R, V> =
    mapKeysTo(LinkedArrayHashMap<R, V>(size), transform)

inline fun <K, V, R : MutableMap<K, V>> Map<out K, V>.filterKeysTo(result: R, predicate: (K) -> Boolean): R {
    this.forEachEntryInline { (key, value) ->
        if (predicate(key)) {
            result.put(key, value)
        }
    }
    return result
}

inline fun <K, V> Map<out K, V>.filterKeys(predicate: (K) -> Boolean): Map<K, V> =
    filterKeysTo(LinkedArrayHashMap<K, V>(), predicate)

inline fun <K, V> Map<out K, V>.filterValues(predicate: (V) -> Boolean): Map<K, V> {
    val result = LinkedArrayHashMap<K, V>()
    for (entry in this) {
        if (predicate(entry.value)) {
            result.put(entry.key, entry.value)
        }
    }
    return result
}

inline fun <K, V> Map<out K, V>.filter(predicate: (Map.Entry<K, V>) -> Boolean): Map<K, V> {
    return filterTo(mutableMapOf<K, V>(), predicate)
}

inline fun <K, V> Map<out K, V>.filterNot(predicate: (Map.Entry<K, V>) -> Boolean): Map<K, V> {
    return filterNotTo(mutableMapOf<K, V>(), predicate)
}

fun <K, V> Iterable<Pair<K, V>>.toMap(): Map<K, V> {
    if (this is Collection) {
        return when (size) {
            0 -> mapOf()
            1 -> mapOf(if (this is List) this[0] else iterator().next())
            else -> toMap(LinkedHashMap<K, V>(size))
        }
    }
    return toMap(LinkedArrayHashMap<K, V>())
}

/**
 * Kotlin's toMap function returns an immutable copy.  The stdlib immplementation just blindly copies the map, but this
 * is unnecessary if the map is immutable to begin with, or we can extract an immutalble snapshot.
 */
@Suppress("UNCHECKED_CAST")
fun <@Treapable K, V> Map<out K, V>.toMap(): Map<K, V> =
    this.asTreapMapOrNull().uncheckedAs() ?:
    if (this.size == 0) mapOf() else this.toMutableMap()

@Suppress("UNCHECKED_CAST", "Treapable")
fun <K, V> Map<out K, V>.toMutableMap(): MutableMap<K, V> =
    this.asTreapMapOrNull()?.builder().uncheckedAs() ?: LinkedArrayHashMap(this)

operator fun <@Treapable K, V> Map<out K, V>.plus(pair: Pair<K, V>): Map<K, V> =
    this.toTreapMap().put(pair.first, pair.second)

operator fun <@Treapable K, V> Map<out K, V>.plus(pairs: Iterable<Pair<K, V>>): Map<K, V> =
    this.toTreapMap().mutate { it += pairs }

operator fun <@Treapable K, V> Map<out K, V>.plus(pairs: Array<out Pair<K, V>>): Map<K, V> =
    this.toTreapMap().mutate { it += pairs }

operator fun <@Treapable K, V> Map<out K, V>.plus(pairs: Sequence<Pair<K, V>>): Map<K, V> =
    this.toTreapMap().mutate { it += pairs }

operator fun <@Treapable K, V> Map<out K, V>.plus(map: Map<out K, V>): Map<K, V> =
    this.toTreapMap().putAll(map)

operator fun <@Treapable K, V> Map<out K, V>.minus(key: K): Map<K, V> =
    this.toTreapMap().remove(key)

operator fun <@Treapable K, V> Map<out K, V>.minus(keys: Iterable<K>): Map<K, V> =
    this.toTreapMap().mutate { it -= keys }

operator fun <@Treapable K, V> Map<out K, V>.minus(keys: Array<out K>): Map<K, V> =
    this.toTreapMap().mutate { it -= keys }

operator fun <@Treapable K, V> Map<out K, V>.minus(keys: Sequence<K>): Map<K, V> =
    this.toTreapMap().mutate { it -= keys }

fun <@Treapable K, V : Any> Map<K, V>.union(m: Map<K, V>, merger: (K, V, V) -> V): TreapMap<K, V> =
    this.toTreapMap().union(m, merger)

fun <@Treapable K, V : Any> Map<K, V>.parallelUnion(m: TreapMap<K, V>, parallelThresholdLog2: Int = 4, merger: (K, V, V) -> V): TreapMap<K, V> =
    this.toTreapMap().parallelUnion(m, parallelThresholdLog2, merger)

fun <@Treapable K, V : Any> Map<K, V>.intersect(m: Map<K, V>, merger: (K, V, V) -> V): TreapMap<K, V> =
    this.toTreapMap().intersect(m, merger)

fun <@Treapable K, V : Any> Map<K, V>.parallelIntersect(m: TreapMap<K, V>, parallelThresholdLog2: Int = 4, merger: (K, V, V) -> V): TreapMap<K, V> =
    this.toTreapMap().parallelIntersect(m, parallelThresholdLog2, merger)

fun <@Treapable K, V : Any> Map<K, V>.merge(m: Map<K, V>, merger: (K, V?, V?) -> V?): TreapMap<K, V> =
    this.toTreapMap().merge(m, merger)

fun <@Treapable K, V : Any> Map<K, V>.parallelMerge(m: TreapMap<K, V>, parallelThresholdLog2: Int = 4, merger: (K, V?, V?) -> V?): TreapMap<K, V> =
    this.toTreapMap().parallelMerge(m, parallelThresholdLog2, merger)

fun <@Treapable K, V, U : Any> Map<K, V>.updateValues(transform: (K, V) -> U?): TreapMap<K, U> =
    this.toTreapMap().updateValues(transform)

fun <@Treapable K, V, U : Any> Map<K, V>.parallelUpdateValues(parallelThresholdLog2: Int = 5, transform: (K, V) -> U?): TreapMap<K, U> =
    this.toTreapMap().parallelUpdateValues(parallelThresholdLog2, transform)

fun <@Treapable K, V : Any, U : Any> Map<K, V>.updateEntry(key: K, item: U?, merger: (V?, U?) -> V?) : TreapMap<K, V> =
    this.toTreapMap().updateEntry(key, item, merger)

infix fun <@Treapable K, V> Map<K, V>.zip(m: Map<out K, V>): Sequence<Map.Entry<K, Pair<V?, V?>>> =
    this.toTreapMap().zip(m)

fun <K, V> Map<K, V>?.orEmpty() = this ?: mapOf()

inline fun <K, V> buildMap(@BuilderInference builderAction: MutableMap<K, V>.() -> Unit): Map<K, V> =
    LinkedArrayHashMap<K, V>().apply(builderAction)

inline fun <K, V> buildMap(capacity: Int, builderAction: MutableMap<K, V>.() -> Unit): Map<K, V> =
    LinkedArrayHashMap<K, V>(capacity).apply(builderAction)

