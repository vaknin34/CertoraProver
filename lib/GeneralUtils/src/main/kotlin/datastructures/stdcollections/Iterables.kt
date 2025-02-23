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

import com.certora.collect.*
import datastructures.*
import kotlinx.collections.immutable.ImmutableSet
import kotlinx.collections.immutable.PersistentSet

import kotlin.collections.single as kSingle
import kotlin.collections.singleOrNull as kSingleOrNull

//
// Override some of the kotlin stdlib functions to use our own optimized map and set implementations
//

public fun <T> Iterable<T>.toSet(): Set<T> = when (this) {
    is ImmutableSet<T> -> this
    is PersistentSet.Builder<T> -> build()
    is Collection<T> -> when (size) {
        0 -> emptySet()
        1 -> setOf(if (this is List) this[0] else iterator().next())
        else -> toCollection(LinkedArrayHashSet<T>(size))
    }
    else -> toCollection(LinkedArrayHashSet<T>())
}

public fun <T> Iterable<T>.toUnorderedSet(): Set<T> {
    if (this is Collection) {
        return when (size) {
            0 -> emptyUnorderedSet()
            1 -> unorderedSetOf(if (this is List) this[0] else iterator().next())
            else -> toCollection(ArrayHashSet<T>(size))
        }
    }
    return toCollection(ArrayHashSet<T>())
}

public inline fun <T, R, C : MutableCollection<in R>> Iterable<T>.mapTo(destination: C, transform: (T) -> R): C {
    for (item in this) {
        destination.add(transform(item))
    }
    return destination
}

fun <T> Iterable<T>.stream() = java.util.stream.StreamSupport.stream(this.spliterator(), false)
fun <T> Iterable<T>.parallelStream() = java.util.stream.StreamSupport.stream(this.spliterator(), true)

public fun <T> Iterable<T>.single(): T = when (this) {
    is TreapSet<T> -> this.single()
    else -> kSingle()
}

public fun <T> Iterable<T>.singleOrNull(): T? = when (this) {
    is TreapSet<T> -> this.singleOrNull()
    else -> kSingleOrNull()
}
