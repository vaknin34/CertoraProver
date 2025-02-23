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

package algorithms

import datastructures.MutableReversibleMap
import datastructures.reverseMap
import datastructures.stdcollections.*
import utils.*

/**
 * The classic algorithm with path shortening, but maintains backwards arrows as well, so that calculating the
 * equivalence class of an element is linear in the equivalence class size. Unions and finds are O(1), but equivalence
 * classes are not maintained, but rather calculated on demand.
 *
 * If (as is common) construction happens in one stage, and queries on another, use this class and then call
 * [toImmutable] to get an immutable version that is efficient on all queries.
 */
open class UnionFind<E> private constructor(
    private val parent: MutableReversibleMap<E, E>
) : EquivalenceRelation<E> {

    constructor() : this(MutableReversibleMap())

    /** Returns the representative of the given node */
    @Synchronized
    fun find(e: E): E {

        /**
         * Recursively goes up the tree until the representative, and rewrites all pointers on the path to point to
         * the root.
         */
        fun rep(e: E): E {
            val r = parent[e]!!
            if (r == e) {
                return r
            }
            return rep(r).also {
                parent[e] = it
            }
        }

        return if (e !in parent) {
            parent[e] = e
            e
        } else {
            rep(e)
        }
    }


    fun register(e: E) = find(e)

    @Synchronized
    override fun getSupportingEqualities(): Set<Pair<E, E>> =
        parent.entries
            .filter { (el, rep) -> el != rep }
            .mapToSet { (el, rep) -> el to rep }

    @Synchronized
    override fun toString() =
        getAllEquivalenceClasses().toString()

    @Synchronized
    open fun union(e1: E, e2: E) {
        parent[find(e2)] = find(e1)
    }

    fun union(es: Collection<E>) {
        if (es.isNotEmpty()) {
            val rep = es.first()
            register(rep)
            es.forEach { e ->
                if (e != rep) {
                    union(e, rep)
                }
            }
        }
    }

    @Synchronized
    fun copy() = UnionFind(parent.copy())

    @Synchronized
    fun toImmutable() = EquivalenceRelation(
        getAllElements().associateWith { getRepresentative(it) }
    )

    @Synchronized
    override fun areEqual(e1: E, e2: E) = find(e1) == find(e2)

    @Synchronized
    override fun getEquivalenceClass(e: E): Set<E> {
        // collect all elements going backwards from the representative
        val set = mutableSetOf<E>()
        fun rec(e: E) {
            if (set.add(e)) {
                parent.keysOf(e).forEach {
                    rec(it)
                }
            }
        }
        rec(find(e))
        return set
    }

    @Synchronized
    override fun getAllRepresentatives() =
        getAllElements().filter { parent[it] == it }.toSet()

    @Synchronized
    override fun getAllEquivalenceClasses(): Set<Set<E>> =
        getAllRepresentatives().mapToSet { getEquivalenceClass(it) }

    @Synchronized
    override fun getAllElements(): List<E> = parent.keys.toList()

    @Synchronized
    override fun isRegistered(e: E): Boolean = e in parent

    @Synchronized
    override fun getRepresentative(e: E): E {
        check(isRegistered(e)) { "$e hasn't been registered yet; register it before calling this method" }
        return find(e)
    }
}

interface EquivalenceRelation<E> {
    fun areEqual(e1: E, e2: E): Boolean

    fun getRepresentative(e: E): E

    fun getAllRepresentatives(): Set<E>

    fun getAllEquivalenceClasses(): Set<Set<E>>

    fun getAllElements(): List<E>

    fun getEquivalenceClass(e: E): Set<E>

    fun isRegistered(e: E): Boolean

    fun getSupportingEqualities(): Set<Pair<E, E>>

    /**
     * Creates an immutable equivalence relation of [E]s. Efficient, but precalculates all the equivalence classes upfront.
     * In other words, a [UnionFind] that does not support 'union'...
     *
     * Would it be nice to have this as a persistent data structure?
     *  [https://www.lri.fr/~filliatr/ftp/publis/puf-wml07.pdf]
     * Maybe also check this: [https://jng.imagine27.com/index.php/2012-08-22-144618_purely-functional-data-structures-algorithms-union-find-haskell.html]
     */
    companion object {
        operator fun <E> invoke(nodeToRep: Map<E, E>): EquivalenceRelation<E> = object : EquivalenceRelation<E> {

            private val repToClass by lazy { reverseMap(nodeToRep) }

            override fun getRepresentative(e: E) =
                nodeToRep[e] ?: error("$e not registered in ${javaClass.simpleName}")

            override fun areEqual(e1: E, e2: E) = getRepresentative(e1) == getRepresentative(e2)

            override fun getAllRepresentatives() = repToClass.keys

            override fun getAllEquivalenceClasses() = repToClass.values.toSet()

            override fun getAllElements() = nodeToRep.keys.toList()

            override fun getSupportingEqualities() =
                nodeToRep.entries
                    .filter { (node, rep) -> node != rep }
                    .mapToSet { (node, rep) -> node to rep }

            override fun isRegistered(e: E) = e in nodeToRep

            override fun getEquivalenceClass(e: E) = repToClass[getRepresentative(e)]!!

            override fun toString() = getAllEquivalenceClasses().toString()
        }

        /** Creates an [EquivalenceRelation] where all the keys of [map] that have the same value are equivalent */
        fun <K, V> fromMap(map: Map<K, V>): EquivalenceRelation<K> {
            val nodesToRep = mutableMapOf<K, K>()
            map.keys.groupBy { map[it] }.values // this is the set of equivalence classes
                .forEach { nodeSet ->
                    nodeSet.forEach { node ->
                        nodesToRep[node] = nodeSet[0]!!
                    }
                }
            return EquivalenceRelation(nodesToRep)
        }
    }
}

/**
 * A [UnionFind] which holds for each node a value which is consistent across its equivalence class.
 * This is achieved via calling [mergeValues] when two classes are merged.
 *
 * null plays the role of uninitialized, and so merging will essentially ignore it.
 */
class UnionFindMap<E, V>(val mergeValues: (V, V) -> V) : UnionFind<E>() {
    private fun mergeValuesNullable(v1 : V?, v2: V?) = when {
        v1 == null -> v2
        v2 == null -> v1
        else -> mergeValues(v1, v2)
    }

    private val values = mutableMapOf<E, V>()

    operator fun get(e: E) = values[find(e)]

    /** Sets [value] to [e]'s class */
    operator fun set(e: E, value : V?) {
        val r = find(e)
        if (value == null) {
            values.remove(r)
        } else {
            values[r] = value
        }
    }

    /** Merges the old value of [e]'s class with [value] */
    fun softSet(e: E, value: V?) {
        val r = find(e)
        this[r] = mergeValuesNullable(values[r], value)
    }

    override fun union(e1: E, e2: E) {
        val w1 = get(e1)
        val w2 = get(e2)
        super.union(e1, e2)
        softSet(e1, mergeValuesNullable(w1, w2))
    }
}

