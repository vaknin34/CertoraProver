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

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.AtomicInteger


interface CounterMap<K> {
    operator fun get(key: K): Int

    val keys: Set<K>

    fun add(key: K, by: Int)

    fun plusOne(key: K) =
        add(key, 1)

    fun minusOne(key: K) =
        add(key, -1)

    fun toString(name: String) = "$name:\n" +
        keys.joinToString("\n") { "    $it = ${get(it)}" }

    fun toMap() =
        keys.associateWith { get(it) }

    fun isEmpty() =
        keys.isEmpty()
}

class SimpleCounterMap<K> : CounterMap<K> {
    private val backing = datastructures.stdcollections.mutableMapOf<K, Int>()

    override val keys get() = backing.keys

    val entries get() = backing.entries

    override operator fun get(key: K) =
        backing[key] ?: 0

    override fun add(key: K, by: Int) {
        backing[key] = get(key) + by
    }
}


class ConcurrentCounterMap<K> : CounterMap<K> {
    private val backing = ConcurrentHashMap<K, AtomicInteger>()

    override val keys get() = backing.keys

    override operator fun get(key: K) =
        backing[key]?.get() ?: 0

    override fun add(key: K, by: Int) {
        backing.computeIfAbsent(key) {
            AtomicInteger(0)
        }.addAndGet(by)
    }
}
