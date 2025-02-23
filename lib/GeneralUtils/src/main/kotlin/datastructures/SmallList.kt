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

import utils.uncheckedAs

abstract class SmallList<T> : List<T>, java.io.Serializable {

    override fun toString(): String = joinToString(", ", "[", "]")

    override fun hashCode(): Int {
        var hashCode = 1
        for (i in 0 until size) {
            hashCode = 31 * hashCode + (get(i)?.hashCode() ?: 0)
        }
        return hashCode
    }

    override fun equals(other: Any?): Boolean {
        if (other === this) return true
        if (other !is List<*>) return false
        if (other.size != this.size) return false
        for (i in 0 until size) {
            if (other[i] != this[i]) return false
        }
        return true
    }

    override fun listIterator(index: Int) = object : ListIterator<T> {
        var i = index
        override fun hasNext() = i < size
        override fun nextIndex() = i
        override fun next() = get(i++)
        override fun hasPrevious() = i > 0
        override fun previousIndex() = i - 1
        override fun previous() = get(--i)
    }

    override fun listIterator(): ListIterator<T> = listIterator(0)
    override fun iterator(): Iterator<T> = listIterator()

    override fun subList(fromIndex: Int, toIndex: Int): List<T> {
        if (fromIndex < 0 || toIndex > size || fromIndex > toIndex) {
            throw IndexOutOfBoundsException()
        }
        return object : AbstractList<T>(), java.io.Serializable {
            val from = fromIndex
            override val size = toIndex - fromIndex
            override fun get(index: Int): T = when {
                index < 0 || index >= size -> throw IndexOutOfBoundsException("No element $index in $this")
                else -> this@SmallList.get(index + fromIndex)
            }
        }
    }

    override fun containsAll(elements: Collection<T>): Boolean =
            elements.all { this.contains(it) }

    override fun indexOf(element: T): Int {
        for (i in 0 until size) {
            if (get(i) == element) {
                return i
            }
        }
        return -1
    }

    override fun lastIndexOf(element: T): Int {
        for (i in (0 until size).reversed()) {
            if (get(i) == element) {
                return i
            }
        }
        return -1
    }

    open class Empty<T> internal constructor() : SmallList<T>() {
        open override val size: Int get() = 0
        open override fun isEmpty(): Boolean = true
        open override fun contains(element: T): Boolean = false
        open override fun get(index: Int): T = throw IndexOutOfBoundsException("No element $index in $this")
    }

    open class Of1<T>(private val value0: T) : Empty<T>() {
        open override val size: Int get() = 1
        override fun isEmpty(): Boolean = false
        open override fun contains(element: T): Boolean = element == value0 || super.contains(element)
        open override fun get(index: Int): T = if (index == 0) value0 else super.get(index)
    }

    open class Of2<T>(value0: T, private val value1: T) : Of1<T>(value0) {
        open override val size: Int get() = 2
        open override fun contains(element: T): Boolean = element == value1 || super.contains(element)
        open override fun get(index: Int): T = if (index == 1) value1 else super.get(index)
    }

    open class Of3<T>(value0: T, value1: T, private val value2: T) : Of2<T>(value0, value1) {
        open override val size: Int get() = 3
        open override fun contains(element: T): Boolean = element == value2 || super.contains(element)
        open override fun get(index: Int): T = if (index == 2) value2 else super.get(index)
    }


    open class Of4<T>(value0: T, value1: T, value2: T, private val value3: T) : Of3<T>(value0, value1, value2) {
        open override val size: Int get() = 4
        open override fun contains(element: T): Boolean = element == value3 || super.contains(element)
        open override fun get(index: Int): T = if (index == 3) value3 else super.get(index)
    }


    open class Of5<T>(value0: T, value1: T, value2: T, value3: T, private val value4: T) : Of4<T>(value0, value1, value2, value3) {
        open override val size: Int get() = 5
        open override fun contains(element: T): Boolean = element == value4 || super.contains(element)
        open override fun get(index: Int): T = if (index == 4) value4 else super.get(index)
    }

    companion object {
        private val empty = Empty<Any?>()
        fun <T> Of0() = empty.uncheckedAs<SmallList<T>>()
    }
}

