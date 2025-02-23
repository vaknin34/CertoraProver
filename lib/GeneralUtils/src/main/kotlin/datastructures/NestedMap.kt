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

/**
 * A map from `K1` X `K2` to `V`.
 */
typealias NestedMap<K1, K2, V> = Map<K1, Map<K2, V>>

operator fun <K1, K2, V> NestedMap<K1, K2, V>.get(k1: K1, k2: K2): V? =
    this[k1]?.get(k2)

fun <K1, K2, V> NestedMap<K1, K2, V>.triples() =
    entries.flatMap { (k1, inner) -> inner.entries.map { (k2, v) -> Triple(k1, k2, v) } }

fun <K1, K2, V> NestedMap<K1, K2, V>.forEachEntry(action : (K1, K2, V) -> Unit) {
    forEachEntry { (k1, inner) ->
        inner.forEachEntry { (k2, v) ->
            action(k1, k2, v)
        }
    }
}


typealias MutableNestedMap<K1, K2, V> = MutableMap<K1, MutableMap<K2, V>>

fun <K1, K2, V> mutableNestedMapOf() = mutableMapOf<K1, MutableMap<K2, V>>()

operator fun <K1, K2, V> MutableNestedMap<K1, K2, V>.set(k1: K1, k2: K2, v: V) =
    computeIfAbsent(k1) { mutableMapOf() }.set(k2, v)

fun <K1, K2, V> MutableNestedMap<K1, K2, V>.put(k1: K1, k2: K2, v: V) =
    set(k1, k2, v)

fun <K1, K2, V> MutableNestedMap<K1, K2, V>.removeIf(pred: (K1, K2, V) -> Boolean) {
    for (k1 in keys) {
        this[k1]?.entries?.removeIf { (k2, v) -> pred(k1, k2, v) }
    }
    entries.removeIf { (_, innerMap) -> innerMap.isEmpty() }
}

fun <K1, K2, V> MutableNestedMap<K1, K2, V>.getOrPut(k1: K1, k2: K2, default: () -> V) : V {
    val old = this[k1, k2]
    return if (old == null) {
        val v = default()
        this[k1, k2] = v
        v
    } else {
        old
    }
}


fun <K1, K2, V> buildNestedMap(builderAction: MutableNestedMap<K1, K2, V>.() -> Unit): NestedMap<K1, K2, V> =
    mutableNestedMapOf<K1, K2, V>().apply(builderAction)

