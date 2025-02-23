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

package utils

import datastructures.stdcollections.*

/**
 * An efficient mutable set that is defined on top of an underlying immutable [base] set.
 *
 * For this to function properly, [base] should never change throughout the life-time of this set.
 * Note that to be worth the extra effort, the number of changes made in the set should be significantly smaller
 * then the size of [base].
 */
class MutableDiffSet<E>(val base: Set<E>) : MutableSet<E> {
    private val additions = mutableSetOf<E>()
    private val subtractions = mutableSetOf<E>()

    // an immutable view
    val adds : Set<E> get() = additions
    val subs : Set<E> get() = subtractions

    override val size get() = base.size + additions.size - subtractions.size

    override fun isEmpty() = size == 0

    override fun add(element: E): Boolean {
        if (subtractions.remove(element)) {
            return true
        }
        if (element in base) {
            return false
        }
        return additions.add(element)
    }

    override fun remove(element: E): Boolean {
        if (additions.remove(element)) {
            return true
        }
        if (element in base) {
            return subtractions.add(element)
        }
        return false
    }

    override fun contains(element: E) =
        element in additions || (element in base && element !in subtractions)

    override fun addAll(elements: Collection<E>) =
        elements.map(::add).any()

    override fun containsAll(elements: Collection<E>) =
        elements.all(::contains)

    override fun removeAll(elements: Collection<E>) =
        elements.map(::remove).any()


    override fun iterator() = object : MutableIterator<E> {
        private val it = (base.asSequence().filter { it !in subtractions } + additions.asSequence()).iterator()
        override fun hasNext() = it.hasNext()
        override fun next() = it.next()
        override fun remove() = unsupported("Not implemented")
    }

    override fun retainAll(elements: Collection<E>) =
        unsupported("Not implemented")

    override fun clear() =
        unsupported("Not implemented")
}
