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

/**
 * A two-way mapping between two sets.
 * Internally uses two maps for efficient lookup in either direction.
 */
open class Bijection<L, R> : Map<L, R> {
    protected val forwardMap: MutableMap<L, R> = mutableMapOf()
    protected val backwardMap: MutableMap<R, L> = mutableMapOf()

    override fun containsKey(key: L): Boolean {
        assert(forwardMap.containsKey(key) == backwardMap.containsValue(key))
        return forwardMap.containsKey(key)
    }

    override fun containsValue(value: R): Boolean {
        assert(backwardMap.containsKey(value) == forwardMap.containsValue(value))
        return backwardMap.containsKey(value)
    }

    override fun get(key: L): R? {
        val res = forwardMap[key]
        assert(res == null || backwardMap[res] == key)
        return res
    }

    fun reverseGet(value: R): L? {
        val res = backwardMap[value]
        assert(res == null || forwardMap[res] == value)
        return res
    }

    override val size: Int
        get() = forwardMap.size


    override fun isEmpty(): Boolean = forwardMap.isEmpty()

    override val entries: Set<MutableMap.MutableEntry<L, R>>
        get() = forwardMap.entries
    override val keys: Set<L>
        get() = forwardMap.keys
    override val values: Collection<R>
        get() = backwardMap.keys

    override fun equals(other: Any?): Boolean {
        if (other !is Bijection<*, *>) return false
        return forwardMap.equals(other.uncheckedAs<Bijection<L, R>>().forwardMap)
    }

    override fun hashCode(): Int {
        return forwardMap.hashCode()
    }

    override fun toString(): String = forwardMap.toString()
    /* operator fun set(it: R, value: R) {
        this[it] = value
    } */

    companion object {

        fun <L, R> fromPairs(vararg pairs: Pair<L, R>): Bijection<L, R>  = fromPairs(pairs.toList())

        /**
         * Create a [Bijection] from a set of pairs. Will throw if the set of pairs is not 1:1 (left-unique and
         * right-unique).
         */
        fun <L, R> fromPairs(pairs: Iterable<Pair<L, R>>): Bijection<L, R> {
            val mut = MutableBijection<L, R>()
            pairs.forEach { mut[it.first] = it.second }
            return mut
        }
        /**
         * Create a [Bijection] from a [Map]. Will throw if the map is not injective.
         */
        fun <L, R> fromMap(map: Map<L, R>): Bijection<L, R> {
            val mut = MutableBijection<L, R>()
            mut.putAll(map)
            return mut
        }
    }
}

/**
 * Mutable version of [Bijection].
 * An error is thrown when bijectivity would be violated by a [put].
 */
class MutableBijection<L, R> : MutableMap<L, R>, Bijection<L, R>() {

    override fun clear() {
        forwardMap.clear()
        backwardMap.clear()
    }

    override fun put(key: L, value: R): R? {
        check(!backwardMap.containsKey(value) || backwardMap[value] == key) { "bijection property violated for $key, $value, ${backwardMap[value]}" }
        val oldValue = forwardMap[key]
        if (oldValue != null) backwardMap.remove(oldValue)
        backwardMap[value] = key
        return forwardMap.put(key, value)
    }

    override fun putIfAbsent(key: L, value: R): R? {
        val existingValue = forwardMap[key]
        return if (existingValue == null) {
            put(key, value)
            null
        } else {
            existingValue
        }
    }

    override fun putAll(from: Map<out L, R>) {
        from.entries.forEach { (key, value) -> put(key, value) }
    }

    override fun remove(key: L): R? {
        val value = forwardMap[key]
        val bwVal = backwardMap.remove(value)
        assert(bwVal == key)
        return forwardMap.remove(key)
    }

    override val entries: MutableSet<MutableMap.MutableEntry<L, R>>
        get() = forwardMap.entries
    override val keys: MutableSet<L>
        get() = forwardMap.keys
    override val values: MutableCollection<R>
        get() = backwardMap.keys

}