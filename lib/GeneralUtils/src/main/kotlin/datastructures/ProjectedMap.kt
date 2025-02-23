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

import com.certora.collect.*
import datastructures.stdcollections.*
import kotlinx.collections.immutable.ImmutableSet
import utils.*

/**
 * Introduces a projected "view" of the map [wrapped] where the values of type [V] are (partially) transformed via the
 * [narrow] function. Keys associated with values for which [narrow] returns null are effectively hidden in the
 * projected map.
 *
 * In addition, this map supports "updates" to the projected map representation via the [merge] function. When adding
 * a binding (k,u) on a ProjectedMap, the [merge] function is called on the current (full) value associated with k
 * in [wrapped] (or null if it doesn't exist). In other words, `proj + (k to u)` is automatically translated to
 * `proj.wrapped + (k to merge(proj.wrapped.get(k), u))`, except if merge returns null, then the binding for `k` is removed.
 *
 * Similarly, removal `proj - k` is translated to `proj.wrapped + (k to merge(m.wrapped.get(k), null))`, where again if
 * merge returns null the binding for `k` is similarly removed.
 *
 * It is expected that [merge] is "coherent" with [narrow], as defined by forall v: U, u: V.narrow(merge(v, u)) == u.
 * This is not a strict requirement, although the behavior of this map can be surprising if this property does not hold.
 * For example, keys can mysteriously fail to appear in the map after being explicitly added, as would be the case
 * with the following merge and narrow functions:
 * narrow = { x: Int -> x.takeIf { it % 2 == 0 } }
 * merge = { _, u -> u }
 *
 * Any odd values added to the map will be properly reflected in [wrapped] but fail to materialize in the projected view.
 * This is a feature or a bug.
 */
class ProjectedMap<@Treapable K, V: Any, U: Any>(val wrapped: TreapMap<K, V>, val narrow: (V) -> U?, val merge : (V?, U?) -> V?) : Map<K, U> {
    private class ProjectionEntry<K, V>(override val key: K, override val value: V) : AbstractMapEntry<K, V>()

    private fun V.hasValue() : Boolean = narrow(this) != null

    override val entries: Set<Map.Entry<K, U>>
        get() = object : ImmutableSet<Map.Entry<K, U>>, AbstractSet<Map.Entry<K, U>>() {
            override val size: Int
                get() = this@ProjectedMap.size

            override fun iterator(): Iterator<Map.Entry<K, U>> = sequence {
                wrapped.forEachEntryInline { (k, v) ->
                    narrow(v)?.also { u ->
                        yield(ProjectionEntry(k, u))
                    }
                }
            }.iterator()

            override fun contains(element: Map.Entry<K, U>): Boolean {
                val m = wrapped.get(element.key) ?: return false
                return narrow(m) == element.value
            }
        }
    override val keys: Set<K>
        get() = object : ImmutableSet<K>, AbstractSet<K>() {
            override val size: Int
                get() = this@ProjectedMap.size

            override fun iterator(): Iterator<K> = sequence {
                wrapped.forEachEntryInline { (k, v) ->
                    if(v.hasValue()) {
                        yield(k)
                    }
                }
            }.iterator()

            override fun contains(element: K): Boolean {
                return this@ProjectedMap.contains(element)
            }

            override fun isEmpty(): Boolean {
                return wrapped.isEmpty() || !iterator().hasNext()
            }
        }

    override val size: Int
        get() = wrapped.entries.count {
            it.value.hasValue()
        }
    override val values: Collection<U>
        get() = entries.map {
            it.value
        }

    override fun isEmpty(): Boolean {
        return wrapped.isEmpty() || wrapped.asSequence().none {
            narrow(it.value) != null
        }
    }

    override fun get(key: K): U? {
        return this.wrapped.get(key)?.let(narrow)
    }

    override fun containsValue(value: U): Boolean {
        return this.wrapped.entries.any {
            narrow(it.value) == value
        }
    }

    override fun containsKey(key: K): Boolean {
        return wrapped[key]?.let { narrow(it) != null } ?: false
    }

    fun mapValues(transform: (Map.Entry<K, U>) -> U): ProjectedMap<K, V, U> = entries.fold(this) { newMap, entry ->
        when (val transformed = transform(entry)) {
            entry.value -> newMap
            else -> newMap + (entry.key to transformed)
        }
    }

    operator fun plus(kv: Pair<K, U>) : ProjectedMap<K, V, U> = ProjectedMap(wrapped.updateEntry(kv.first, kv.second, merge), narrow, merge)
    operator fun minus(k: K) : ProjectedMap<K, V, U> = ProjectedMap(wrapped.updateEntry(k, null, merge), narrow, merge)
}
