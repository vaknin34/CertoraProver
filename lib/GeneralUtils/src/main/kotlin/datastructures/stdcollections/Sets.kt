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
import kotlinx.collections.immutable.PersistentSet
import utils.*

//
// Make it easy to convert Java sets to ArrayHashSet
//
fun <E, S : Set<E>> S.toPreferredSet() =
    when (this) {
        is LinkedHashSet<*> -> LinkedArrayHashSet<E>(this as Set<E>)
        is HashSet<*> -> ArrayHashSet<E>(this as Set<E>)
        else -> this // we don't know the behavior of arbitrary set types, so leave them as is.
    }

//
// Override some of the kotlin stdlib functions to use our own optimized set implementation
//
fun <T> setOf(): Set<T> = kotlin.collections.setOf() //use the built-in empty set implementation

fun <T> setOf(element: T): Set<T> = kotlin.collections.setOf(element)

fun <T> setOf(vararg elements: T): Set<T> =
    if (elements.size > 0) elements.toSet() else setOf()

fun <T> mutableSetOf(): MutableSet<T> = LinkedArrayHashSet<T>()

fun <T> mutableSetOf(vararg elements: T): MutableSet<T> =
    elements.toCollection(LinkedArrayHashSet<T>(elements.size))

fun <T : Any> setOfNotNull(element: T?): Set<T> =
    if (element != null) setOf(element) else setOf()

fun <T : Any> setOfNotNull(vararg elements: T?): Set<T> =
    elements.filterNotNullTo(mutableSetOf())

fun <T : Any> mutableSetOfNotNull(vararg elements: T?): MutableSet<T> =
    elements.filterNotNullTo(mutableSetOf())

inline fun <E> Set<E>.forEach(action: (element: E) -> Unit): Unit {
    when (this) {
        is ArrayHashSet<E> ->
            this.forEach(action)
        is LinkedArrayHashSet<E> ->
            this.forEach(action)
        else ->
            for (e in this) {
                action(e)
            }
    }
}

/**
  This is like [forEach], but the action is not inlined.  This allows us to optimize for [TreapSet]s - we can simply
  traverse the tree, without having to maintain a stack, state machine, etc.
 */
fun <T> Set<T>.forEachElement(action: (element: T) -> Unit): Unit =
    this.asTreapSetOrNull()?.forEachElement(action) ?: this.forEach(action)

fun <T> Iterable<T>.toMutableSet(): MutableSet<T> =
    this.asPersistentSetOrNull()?.builder() ?:
    (this as? Collection<T>)?.let { LinkedArrayHashSet<T>(it) } ?:
    this.toCollection(LinkedArrayHashSet<T>())

fun <T> emptyUnorderedSet(): Set<T> = setOf()
fun <T> unorderedSetOf(): Set<T> = setOf()
fun <T> unorderedSetOf(element: T): Set<T> = setOf(element)
fun <T> unorderedSetOf(vararg elements: T): Set<T> =
    if (elements.size > 0) elements.toUnorderedSet() else setOf()

fun <T> mutableUnorderedSetOf(): MutableSet<T> = ArrayHashSet<T>()
fun <T> mutableUnorderedSetOf(vararg elements: T): MutableSet<T> =
    elements.toCollection(ArrayHashSet<T>(elements.size))

fun <T> Set<T>?.orUnorderedEmpty() = this ?: setOf<T>()

operator fun <@Treapable T> Set<T>.minus(element: T): Set<T> =
    this.toTreapSet().remove(element)

operator fun <@Treapable T> Set<T>.minus(elements: Array<out T>): Set<T> =
    this.toTreapSet().mutate { it.removeAll(elements) }

operator fun <@Treapable T> Set<T>.minus(elements: Iterable<T>): Set<T> =
    this.toTreapSet().mutate { it.removeAll(elements) }

operator fun <@Treapable T> Set<T>.minus(elements: Sequence<T>): Set<T> =
    this.toTreapSet().mutate { it.removeAll(elements) }

fun <@Treapable T> Set<T>.minusElement(element: T): Set<T> = minus(element)

operator fun <@Treapable T> Set<T>.plus(element: T): Set<T> =
    this.toTreapSet().add(element)

operator fun <@Treapable T> Set<T>.plus(elements: Array<out T>): Set<T> =
    this.toTreapSet().mutate { it.addAll(elements) }

operator fun <@Treapable T> Set<T>.plus(elements: Iterable<T>): Set<T> =
    this.toTreapSet().mutate { it.addAll(elements) }

operator fun <@Treapable T> Set<T>.plus(elements: Sequence<T>): Set<T> =
    this.toTreapSet().mutate { it.addAll(elements) }

fun <@Treapable T> Set<T>.plusElement(element: T): Set<T> = plus(element)

infix fun <@Treapable T> Iterable<T>.intersect(other: Iterable<T>): Set<T> =
    this.toTreapSet().mutate { it.retainAll(other) }

infix fun <@Treapable T> Iterable<T>.union(other: Iterable<T>): Set<T> =
    this.toTreapSet().mutate { it.addAll(other) }

@Suppress("HashCodeStability")
private fun <T> Iterable<T>?.asPersistentSetOrNull(): PersistentSet<T>? =
    this as? PersistentSet<T> ?:
    (this as? PersistentSet.Builder<T>)?.build()

@Suppress("HashCodeStability")
private fun <T> Iterable<T>?.asTreapSetOrNull(): TreapSet<T>? =
    this as? TreapSet<T> ?:
    ((this as? PersistentSet.Builder<T>)?.build() as? TreapSet<T>)

fun <@Treapable T> PersistentSet<T>?.orEmpty(): Set<T> = this ?: treapSetOf()

fun <T> Set<T>.findEqual(element: T): T? {
    this.asTreapSetOrNull()?.let {
        return it.findEqual(element)
    }
    this.forEach {
        if (it == element) {
            return it
        }
    }
    return null
}

fun <T> Set<T>.containsAny(predicate: (T) -> Boolean): Boolean =
    this.asTreapSetOrNull()?.let { it.containsAny(predicate) } ?: this.any(predicate)
