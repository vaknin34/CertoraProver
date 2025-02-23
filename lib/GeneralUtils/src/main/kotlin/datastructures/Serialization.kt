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

// If we ever change the way sets are serialized, we need to change this to a different number (and make sure
// deserialization works for the previous version as well)
const val setSerialVersionUID: Long = 1

fun <E> java.io.ObjectOutputStream.writeSet(set: Set<E>, loadFactor: Float) {
    writeInt(set.size)
    writeFloat(loadFactor)
    for (e in set) {
        writeObject(e)
    }
}

fun <E> java.io.ObjectInputStream.readSet(builder: (Int, Float) -> MutableSet<E>) {
    val size = readInt()
    val loadFactor = readFloat()
    val set = builder(size, loadFactor)
    repeat(size) {
        @Suppress("UNCHECKED_CAST")
        set.add(readObject() as E)
    }
}

// If we ever change the way maps are serialized, we need to change this to a different number (and make sure
// deserialization works for the previous version as well)
const val mapSerialVersionUID: Long = 1

fun <K, V> java.io.ObjectOutputStream.writeMap(map: Map<K, V>, loadFactor: Float) {
    writeInt(map.size)
    writeFloat(loadFactor)
    for (e in map.entries) {
        writeObject(e.key)
        writeObject(e.value)
    }
}

fun <K, V> java.io.ObjectInputStream.readMap(builder: (capacity: Int, loadFactor: Float) -> MutableMap<K, V>) {
    val size = readInt()
    val loadFactor = readFloat()
    val map = builder(size, loadFactor)
    repeat(size) {
        @Suppress("UNCHECKED_CAST")
        val key = readObject() as K;
        @Suppress("UNCHECKED_CAST")
        val value = readObject() as V;

        map.put(key, value)
    }
}
