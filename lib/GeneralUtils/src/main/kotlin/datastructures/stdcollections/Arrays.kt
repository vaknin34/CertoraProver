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

fun <K, V> Array<out Pair<K, V>>.toMap(): Map<K, V> = when (size) {
    0 -> mapOf()
    1 -> mapOf(this[0])
    else -> toMap(LinkedArrayHashMap<K, V>(size))
}

public fun <T> Array<out T>.toSet(): Set<T> {
    return when (size) {
        0 -> emptySet()
        1 -> setOf(this[0])
        else -> toCollection(LinkedArrayHashSet<T>(size))
    }
}

public fun <T> Array<out T>.toUnorderedSet(): Set<T> {
    return when (size) {
        0 -> emptyUnorderedSet()
        1 -> unorderedSetOf(this[0])
        else -> toCollection(ArrayHashSet<T>(size))
    }
}

fun <T> Array<out T>.toMutableSet(): MutableSet<T> =
    toCollection(LinkedArrayHashSet<T>(size))

fun <T> Array<out T>.toMutableUnorderedSet(): MutableSet<T> =
    toCollection(ArrayHashSet<T>(size))

