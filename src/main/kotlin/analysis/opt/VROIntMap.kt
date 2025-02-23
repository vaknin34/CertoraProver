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

package analysis.opt

import analysis.opt.numeric.*
import com.certora.collect.*
import datastructures.stdcollections.*
import vc.data.*

/**
    Maps vars to VROInts, and maintains an index of related vars to speedup the "kill" operation.

    This type is immutable, and all operations return a new instance.  Use [builder] for in-place updates.
 */
class VROIntMap private constructor(
    val ints: TreapMap<TACSymbol.Var, VROInt>,
    /**
        Maps var v to a set of vars u for which u.qual.any { it.relates(v) } might be true.  I.e., a set of vars whose
        qualifiers might need to be modified if v is killed.
     */
    val relatedIndex: TreapMap<TACSymbol.Var, TreapSet<TACSymbol.Var>>,
) : Map<TACSymbol.Var, VROInt> by ints {

    constructor() : this(treapMapOf(), treapMapOf())

    override fun equals(other: Any?) = other is VROIntMap && this.ints == other.ints
    override fun hashCode() = ints.hashCode()
    override fun toString() = ints.toString()

    fun forEachEntry(action: (Map.Entry<TACSymbol.Var, VROInt>) -> Unit) = ints.forEachEntry(action)

    fun snapshot() = VROIntMap(ints, relatedIndex)

    operator fun plus(p: Pair<TACSymbol.Var, VROInt>): VROIntMap {
        val (v, i) = p
        return when {
            i == ints[v] -> this
            else -> VROIntMap(
                ints = ints + p,
                relatedIndex = relatedIndex.addRelated(v, i)
            )
        }
    }

    fun kill(v: TACSymbol.Var) = when {
        v !in ints -> this
        else -> VROIntMap(
            ints = removeFromInts(v),
            relatedIndex = relatedIndex - v
        )
    }

    /** Removes [v] without updating any quals. */
    fun forget(v: TACSymbol.Var) = when {
        v !in ints -> this
        else -> VROIntMap(
            ints = ints - v,
            relatedIndex = relatedIndex - v
        )
    }

    fun merge(m: VROIntMap, merger: (TACSymbol.Var, VROInt?, VROInt?) -> VROInt?): VROIntMap {
        var newRelatedIndex = treapMapOf<TACSymbol.Var, TreapSet<TACSymbol.Var>>()
        val newInts = ints.merge(m.ints) { v, i1, i2 ->
            merger(v, i1, i2)?.also { newInt ->
                newRelatedIndex = newRelatedIndex.addRelated(v, newInt)
            }
        }
        return VROIntMap(newInts, newRelatedIndex)
    }

    fun intersect(m: VROIntMap, merger: (TACSymbol.Var, VROInt, VROInt) -> VROInt): VROIntMap {
        var newRelatedIndex = treapMapOf<TACSymbol.Var, TreapSet<TACSymbol.Var>>()
        val newInts = ints.intersect(m.ints) { v, i1, i2 ->
            merger(v, i1, i2).also { newInt ->
                newRelatedIndex = newRelatedIndex.addRelated(v, newInt)
            }
        }
        return VROIntMap(newInts, newRelatedIndex)
    }

    fun builder() = Builder(ints.builder(), relatedIndex.builder())

    /** Removes [v] from [ints], and from all quals for which q.relates(v) */
    private fun removeFromInts(v: TACSymbol.Var) = (ints - v).mutate { ints ->
        relatedIndex[v]?.forEachElement {
            ints[it]?.let { i ->
                ints[it] = i.copy(qual = i.qual.removeAll { q -> q.relates(v) })
            }
        }
    }

    /** Updates relatedIndex from the new quals for [v] */
    private fun TreapMap<TACSymbol.Var, TreapSet<TACSymbol.Var>>.addRelated(
        v: TACSymbol.Var,
        i: VROInt
    ): TreapMap<TACSymbol.Var, TreapSet<TACSymbol.Var>> {
        var relatedIndex = this
        i.qual.forEachElement {
            it.related.forEachElement { r ->
                relatedIndex = relatedIndex.updateEntry(r, v) { old, new -> old.orEmpty() + new }
            }
        }
        return relatedIndex
    }

    class Builder(
        val ints: TreapMap.Builder<TACSymbol.Var, VROInt>,
        val relatedIndex: TreapMap.Builder<TACSymbol.Var, TreapSet<TACSymbol.Var>>
    ) : Map<TACSymbol.Var, VROInt> by ints {
        fun updateInPlace(v: TACSymbol.Var, default: VROInt, f: (VROInt) -> VROInt) {
            val oldInt = ints[v]
            val newInt = f(oldInt ?: default)

            if (newInt != oldInt) {
                ints[v] = newInt
                newInt.qual.forEachElement {
                    it.related.forEachElement { r ->
                        relatedIndex[r] = relatedIndex.getOrDefault(r, treapSetOf()) + v
                    }
                }
            }
        }

        fun build() = VROIntMap(ints.build(), relatedIndex.build())
    }
}

fun VROIntMap?.orEmpty() = this ?: VROIntMap()

