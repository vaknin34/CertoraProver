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

package datastructures

import datastructures.stdcollections.*
import java.util.EnumSet as RawEnumSet

/**
 * A set of enum values.  Some Set operations in [datastructures.stdcollections] do not support enum values, because
 * they require types with hash codes that are stable across JVM instances.  If you need a set of enums, use this
 * class instead.  Note that this class intentionally does *not* implement Set<T>, as that would make it too easy
 * to run afoul of the stdcollections Set operations.
 */
@JvmInline value class EnumSet<T : Enum<T>> @PublishedApi internal constructor(val set: RawEnumSet<T>) : Iterable<T>, Collection<T> {
    override fun iterator() = set.iterator()

    override fun isEmpty() = set.isEmpty()
    fun isNotEmpty() = !isEmpty()
    override val size
        get() = set.size
    override operator fun contains(element: T) = set.contains(element)
    fun containsAny(elements: Iterable<T>) = elements.any { it in this }
    override fun containsAll(elements: Collection<T>) = set.containsAll(elements)
    operator fun plus(element: T) = EnumSet(set.clone().apply { add(element) })
    operator fun plus(elements: Iterable<T>) = EnumSet(set.clone().apply { addAll(elements) })

    operator fun minus(element: T) = EnumSet<T>(set.clone().apply { remove(element) })
    operator fun minus(elements: Iterable<T>) = EnumSet(set.clone().apply { removeAll(elements) })
}

inline fun <reified T : Enum<T>> enumSetOf() =
    EnumSet(RawEnumSet.noneOf(T::class.java))

inline fun <reified T : Enum<T>> enumSetOf(vararg elements: T) =
    EnumSet(RawEnumSet.noneOf(T::class.java).apply { addAll(elements) })

inline fun <reified T : Enum<T>> enumSetOf(elements: Collection<T>) =
    EnumSet(RawEnumSet.noneOf(T::class.java).apply { addAll(elements) })
