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

import datastructures.arrayhashtable.*
import kotlinx.serialization.Serializable

@Suppress("UNCHECKED_CAST")
@Serializable(with = LinkedArrayHashSetSerializer::class)
class LinkedArrayHashSet<E>(
        initialCapacity: Int = ArrayHashTable.defaultCapacity, 
        override var loadFactor: Float = ArrayHashTable.defaultLoadFactor
) : AbstractMutableSet<E>(), ArrayHashTableContainer, java.io.Serializable {

    override val isOrdered
        get() = true
    override val hasValues
        get() = false
    override var hashTable = createArrayHashTable(this, initialCapacity)

    constructor(other: Collection<E>) : this(other.size) {
        hashTable._initFromOrdered(other)
    }

    companion object {
        private const val serialVersionUID = setSerialVersionUID
    }

    @Throws(java.io.IOException::class)
    private fun writeObject(out: java.io.ObjectOutputStream) {
        out.writeSet(this, loadFactor)
    }

    @Throws(java.io.IOException::class, ClassNotFoundException::class)
    private fun readObject(inn: java.io.ObjectInputStream) {
        inn.readSet { c, l ->
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
    override fun iterator() = hashTable._orderedKeyIterator() as MutableIterator<E>
    override fun add(element: E) = hashTable._addKeyOrdered(element)
    override fun contains(element: E) = hashTable._containsKey(element)
    override fun remove(element: E): Boolean = hashTable._removeKeyOrdered(element)

    override fun addAll(elements: Collection<E>) = hashTable._addAllKeys(elements)
    override fun removeAll(elements: Collection<E>) = hashTable._removeAllKeys(elements)
    override fun retainAll(elements: Collection<E>) = hashTable._removeAllKeysExcept(elements)

    inline fun forEach(action: (element: E) -> Unit) = 
        hashTable._forEachKeyOrdered {
            action(it as E)
        }
}
