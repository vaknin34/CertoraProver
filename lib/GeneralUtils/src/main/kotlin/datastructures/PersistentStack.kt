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

import utils.*

/**
  A stack, represented in a way that allows functional push/pop operations with maximal memory reuse.
  (Shhh...it's a linked list.)
 */
sealed interface PersistentStack<T>: Iterable<T> {
    fun isEmpty(): Boolean
    val size: Int

    val top: T
    fun pop(): PersistentStack<T>
    fun push(value: T): PersistentStack<T>

    override fun iterator(): Iterator<T> = sequence { forEachElement { yield(it) }}.iterator()

    fun builder(): Builder<T> = PersistentStackBuilder(this)

    /**
      A "builder," providing in-place mutations over a PersistentStack.
     */
    sealed interface Builder<T> : Iterable<T> {
        fun build(): PersistentStack<T>
        fun isEmpty(): Boolean
        val size: Int
        val top: T
        fun pop(): T
        fun pop(popCount: Int): List<T>
        fun push(value: T)
        fun pushAll(values: Iterable<T>)
    }
}

/** A concrete PersistentStack.Builder */
private class PersistentStackBuilder<T>(
    private var stack: PersistentStack<T>
) : PersistentStack.Builder<T> {
    override val size get() = stack.size

    override fun build() = stack
    override fun isEmpty() = stack.isEmpty()
    override val top get() = stack.top
    override fun pop() = top.also { stack = stack.pop() }
    override fun pop(popCount: Int) = stack.peek(popCount).also { stack = stack.pop(popCount) }
    override fun push(value: T) { stack = stack.push(value) }
    override fun pushAll(values: Iterable<T>) { values.forEach { push(it) } }
    override fun iterator() = stack.iterator()
    override fun toString() = stack.toString()
    override fun hashCode() = stack.hashCode()
    override fun equals(other: Any?) = stack.persistentStackEquals(other)
}

/** A node in a a PersistentStack */
private class LinkedPersistentStack<T>(
    override val top: T,
    override val size: Int,
    private val next: PersistentStack<T>
) : PersistentStack<T> {
    override fun isEmpty() = false
    override fun pop() = next
    override fun push(value: T): PersistentStack<T> = LinkedPersistentStack(value, size + 1, this)

    override fun equals(other: Any?) = persistentStackEquals(other)
    override fun hashCode() = persistentStackHashCode()
    override fun toString() = persistentStackToString()
}

/** Empty persistent stack base case. */
private class EmptyPersistentStack<T> private constructor() : PersistentStack<T> {
    override fun isEmpty() = true
    override val size = 0
    override val top: T get() = error("Empty stack")
    override fun pop(): PersistentStack<T> = error("Empty stack")
    override fun push(value: T): PersistentStack<T> = LinkedPersistentStack<T>(value, 1, this)

    override fun equals(other: Any?) = this === other
    override fun hashCode() = 0
    override fun toString() = persistentStackToString()

    companion object {
        private val instance = EmptyPersistentStack<Nothing>()
        operator fun <T> invoke() = instance.uncheckedAs<EmptyPersistentStack<T>>()
    }
}

inline fun <T> PersistentStack<T>.forEachElement(action: (T) -> Unit) {
    var current = this
    while (!current.isEmpty()) {
        action(current.top)
        current = current.pop()
    }
}

private fun <T> PersistentStack<T>.persistentStackEquals(other: Any?): Boolean = when {
    other === this -> true
    other is PersistentStack.Builder<*> -> persistentStackEquals(other.build())
    other !is PersistentStack<*> -> false
    else -> persistentStackEquals(other)
}

private tailrec fun <T> PersistentStack<T>.persistentStackEquals(other: PersistentStack<*>): Boolean = when {
    other === this -> true
    this.isEmpty() && other.isEmpty() -> true
    this.size != other.size -> false
    this.top != other.top -> false
    else -> this.pop().persistentStackEquals(other.pop())
}


private fun <T> PersistentStack<T>.persistentStackHashCode(): Int {
    var h = 0
    forEachElement {
        h = 31 * h + it.hashCode()
    }
    return h
}

private fun <T> PersistentStack<T>.persistentStackToString(): String =
    joinToString(", ", "[", "]") {
        if (it === this) "(this Collection)" else it.toString()
    }

/** Remaps the contents of a stack, reusing memory where possible. */
inline fun <T, R> PersistentStack<T>.updateValues(transform: (Int, T) -> R): PersistentStack<R> {
    var unreversed = this
    var reversed = persistentStackOf<PersistentStack<T>>()
    while (!unreversed.isEmpty()) {
        reversed = reversed.push(unreversed)
        unreversed = unreversed.pop()
    }

    var result = persistentStackOf<R>()
    while (!reversed.isEmpty()) {
        val t = reversed.top
        val r = transform(t.size, t.top)
        if (result === t.pop() && r == t.top) {
            result = t.uncheckedAs()
        } else {
            result = result.push(r)
        }
        reversed = reversed.pop()
    }

    return result
}

/** Pops multiple values */
fun <T> PersistentStack<T>.pop(popCount: Int): PersistentStack<T> {
    var s = this
    repeat(popCount) {
        s = s.pop()
    }
    return s
}

fun <T> PersistentStack<T>.popOrNull() = if (isEmpty()) null else pop()

/** Pushes multiple values */
fun <T> PersistentStack<T>.pushAll(values: Iterable<T>): PersistentStack<T> {
    var s = this
    for (v in values) {
        s = s.push(v)
    }
    return s
}

fun <T> persistentStackOf(): PersistentStack<T> = EmptyPersistentStack<T>()
fun <T> PersistentStack<T>?.orEmpty(): PersistentStack<T> = this ?: persistentStackOf()

fun <T> PersistentStack<T>.topOrNull() = if (isEmpty()) { null } else { top }
