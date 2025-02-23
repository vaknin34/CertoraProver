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

import com.certora.collect.MutableMapEntry
import datastructures.arrayhashtable.ArrayHashTable
import datastructures.arrayhashtable.ArrayHashTableContainer
import datastructures.arrayhashtable.createArrayHashTable
import kotlinx.serialization.Serializable

@Suppress("UNCHECKED_CAST")
@Serializable(with = ArrayHashMapSerializer::class)
class ArrayHashMap<K, V>(
        initialCapacity: Int = ArrayHashTable.defaultCapacity,
        override var loadFactor: Float = ArrayHashTable.defaultLoadFactor
) : AbstractMutableMap<K, V>(), ArrayHashTableContainer, java.io.Serializable {

    override val isOrdered
        get() = false
    override val hasValues
        get() = true
    override var hashTable = createArrayHashTable(this, initialCapacity)

    constructor(other: Map<out K, V>) : this(other.size) {
        hashTable._initFrom(other)
    }

    companion object {
        private const val serialVersionUID = mapSerialVersionUID
    }

    private fun writeObject(out: java.io.ObjectOutputStream) {
        out.writeMap(this, loadFactor)
    }

    private fun readObject(inn: java.io.ObjectInputStream) {
        inn.readMap { c, l ->
            apply {
                loadFactor = l
                hashTable = createArrayHashTable(this, c)
            }
        }
    }

    override val size
        get() = hashTable.count
    override fun isEmpty() = hashTable.count == 0
    override fun clear() = hashTable.reset()
    override fun put(key: K, value: V): V? = hashTable._addValue(key, value) as V?
    override fun containsKey(key: K): Boolean = hashTable._containsKey(key)
    override fun containsValue(value: V): Boolean = hashTable._containsValue(value)
    override fun get(key: K): V? = hashTable._getValueOrDefault(key, null) as V?
    override fun getOrDefault(key: K, defaultValue: @UnsafeVariance V): V =
            hashTable._getValueOrDefault(key, defaultValue) as V
    override fun remove(key: K): V? = hashTable._removeValue(key) as V?
    override fun remove(key: K, value: V): Boolean = hashTable._removeValue(key, value)

    private inner class EntryIterator : MutableIterator<MutableMap.MutableEntry<K, V>> {
        val keyIterator = hashTable._keyIterator()
        override fun hasNext() = keyIterator.hasNext()
        override fun next() = MutableMapEntry(this@ArrayHashMap, keyIterator.next() as K)
        override fun remove() = keyIterator.remove()
    }

    private inner class EntrySet : AbstractMutableSet<MutableMap.MutableEntry<K, V>>() {
        override val size
            get() = hashTable.count
        override fun clear() = hashTable.reset()
        override fun add(element: MutableMap.MutableEntry<K, V>): Boolean = throw UnsupportedOperationException()
        override fun iterator(): MutableIterator<MutableMap.MutableEntry<K, V>> = EntryIterator()
    }

    override val entries: MutableSet<MutableMap.MutableEntry<K, V>>
        get() = EntrySet()

    inline fun forEachEntry(action: (key: K, value: V) -> Unit): Unit =
        hashTable._forEachValue { k, v ->
            action(k as K, v as V)
        }

    fun putIfAbsent(key: K, value: V): V? = hashTable._addValueIfAbsent(key, value) as V?

    fun computeIfAbsent(key: K, f: (K) -> V): V = hashTable._computeValueIfAbsent(key) { f(it as K) } as V
}
