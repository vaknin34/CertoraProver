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
import utils.*
import java.util.concurrent.ConcurrentHashMap


/**
 * Just a nice wrapper around `getOrPut` - and it behaves like a function. So it's quite elegant to use.
 * For example:
 * ```
 * val f = Memoized { i : Int -> i * i }
 * ```
 * use `f` as a function (although it's a val), and the multiplication won't be recalculated every time.
 *
 * Note:
 *   [K] can't be nullable because of [ConcurrentHashMap].
 *   [V] can't be nullable because of the behavior of `computeIfAbsent`.
 *   If you need [V] to be nullable, use [NullableMemoized] below.
 */
open class Memoized<K : Any, V : Any>(val concurrent: Boolean = true, val f: (K) -> V) {
    private val cache: MutableMap<K, V> =
        if (concurrent) {
            ConcurrentHashMap()
        } else {
            mutableMapOf()
        }

    operator fun invoke(k: K): V = cache.computeIfAbsent(k) { f(k) }
}

class Memoized2<K1, K2, V : Any>(concurrent: Boolean = true, f: (K1, K2) -> V)
    : Memoized<Pair<K1, K2>, V>(concurrent, f = { pair -> f(pair.first, pair.second) }) {
        operator fun invoke(k1: K1, k2 : K2): V = invoke(k1 to k2)
    }


/**
 * Use this instead of [Memoized] if [V] is nullable.
 */
open class NullableMemoized<K: Any, V>(val concurrent: Boolean = true, val f: (K) -> V) {
    sealed interface R {
        @JvmInline
        value class Value<V>(val v: V) : R
        data object NULL : R
    }

    private val cache : MutableMap<K, R> =
        if (concurrent) {
            ConcurrentHashMap()
        } else {
            mutableMapOf()
        }

    operator fun invoke(k: K): V? =
        cache.computeIfAbsent(k) {
            f(k)?.let { R.Value(it) } ?: R.NULL
        }.let {
            (it as? R.Value<*>)?.v?.uncheckedAs<V>()
        }
}


class NullableMemoized2<K1, K2, V>(concurrent: Boolean = true, f: (K1, K2) -> V)
    : NullableMemoized<Pair<K1, K2>, V>(concurrent, f = { pair -> f(pair.first, pair.second) }) {
    operator fun invoke(k1: K1, k2 : K2): V? = invoke(k1 to k2)
}
