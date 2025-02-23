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

package datastructures.stdcollections
import datastructures.*

//
// Override some of the kotlin stdlib functions to use our own optimized map and set implementations
//

public fun <T> Sequence<T>.toSet(): Set<T> {
    return toCollection(mutableSetOf<T>())
}

public fun <T> Sequence<T>.toUnorderedSet(): Set<T> {
    return toCollection(mutableUnorderedSetOf<T>())
}

public fun <T> Sequence<T>.toMutableSet(): MutableSet<T> {
    return toCollection(mutableSetOf<T>())
}

public fun <T> Sequence<T>.toMutableUnorderedSet(): MutableSet<T> {
    return toCollection(mutableUnorderedSetOf<T>())
}

public inline fun <T, K, V> Sequence<T>.associate(transform: (T) -> Pair<K, V>): Map<K, V> {
    return associateTo(mutableMapOf<K, V>(), transform)
}

public inline fun <T, K> Sequence<T>.associateBy(keySelector: (T) -> K): Map<K, T> {
    return associateByTo(mutableMapOf<K, T>(), keySelector)
}

public inline fun <T, K, V> Sequence<T>.associateBy(keySelector: (T) -> K, valueTransform: (T) -> V): Map<K, V> {
    return associateByTo(mutableMapOf<K, V>(), keySelector, valueTransform)
}

public inline fun <K, V> Sequence<K>.associateWith(valueSelector: (K) -> V): Map<K, V> {
    return associateWithTo(mutableMapOf<K, V>(), valueSelector)
}

public inline fun <T, K> Sequence<T>.groupBy(keySelector: (T) -> K): Map<K, List<T>> {
    return groupByTo(mutableMapOf<K, MutableList<T>>(), keySelector)
}

public inline fun <T, K, V> Sequence<T>.groupBy(keySelector: (T) -> K, valueTransform: (T) -> V): Map<K, List<V>> {
    return groupByTo(mutableMapOf<K, MutableList<V>>(), keySelector, valueTransform)
}

fun <K, V> Sequence<Pair<K, V>>.toMap(): Map<K, V> = toMap(mutableMapOf<K, V>())

