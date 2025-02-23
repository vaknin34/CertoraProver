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

package smtlibutils.algorithms

import algorithms.EquivalenceRelation
import algorithms.UnionFind
import datastructures.add
import datastructures.addAll
import datastructures.getImage
import datastructures.mutableMultiMapOf
import smtlibutils.data.SmtExp

class MutableCongruenceClosure(
    private val uf: UnionFind<SmtExp> = UnionFind()
) : EquivalenceRelation<SmtExp> by uf {

    private val representativeToCcParent =
        mutableMultiMapOf<SmtExp, SmtExp.Apply>()

    fun register(e: SmtExp) {
        if (uf.isRegistered(e)) return
        uf.register(e)
        if (e is SmtExp.Apply) {
            e.args.forEach { registerParent(it, e) }
        }
    }


    fun registerParent(e: SmtExp, parent: SmtExp.Apply) {
        register(e)
        val f = uf.find(e)
        val otherParents =
            representativeToCcParent.getImage(f).toList() // making a copy to avoid concurrent modification
        representativeToCcParent.add(f, parent)
        val toMerge = mutableListOf<Pair<SmtExp, SmtExp>>()
        otherParents.forEach { otherParent ->
            if (uf.find(parent) != uf.find(otherParent) && congruent(parent, otherParent)) {
                toMerge.add(Pair(parent, otherParent))
            }
        }
        toMerge.forEach { (p1, p2) -> mergeEquivalenceClasses(p1, p2) }
    }

    fun mergeEquivalenceClasses(elements: Collection<SmtExp>) {
        if (elements.size < 2) elements.forEach { register(it) }
        val it = elements.iterator()
        if (!it.hasNext()) return
        var current = it.next()
        while (it.hasNext()) {
            val next = it.next()
            mergeEquivalenceClasses(next, current)
            current = next
        }
    }

    fun mergeEquivalenceClasses(e1: SmtExp, e2: SmtExp) {
        register(e1)
        register(e2)

        val f1 = uf.find(e1)
        val f2 = uf.find(e2)
        if (f1 == f2) return

        val parents1 = representativeToCcParent.getImage(f1)
        val parents2 = representativeToCcParent.getImage(f2)
        union(f1, f2)
        val toMerge = mutableListOf<Pair<SmtExp, SmtExp>>()
        parents1.forEach { parent1 ->
            parents2.forEach { parent2 ->
                if (uf.find(parent1) != uf.find(parent2) && congruent(parent1, parent2))
                    toMerge.add(Pair(parent1, parent2))
                //mergeEquivalenceClasses(parent1, parent2)
            }
        }
        toMerge.forEach { (p1, p2) -> mergeEquivalenceClasses(p1, p2) }
    }


    // TODO expecting zip and fold to be inefficient (CERT-8094)
    private fun congruent(e1: SmtExp.Apply, e2: SmtExp.Apply): Boolean =
        e1.fs == e2.fs &&
                e1.args.size == e2.args.size &&
                e1.args.zip(e2.args).fold(true) { ir, (arg1, arg2) -> ir && areEqual(arg1, arg2) }

    fun union(e1: SmtExp, e2: SmtExp) {
        register(e1)
        register(e2)

        /* save old representatives */
        val f1 = uf.find(e1)
        val f2 = uf.find(e2)

        uf.union(f1, f2)

        /* update ccpar */
        val newRep = uf.find(f1)
        val notNewRep = if (newRep == f1) f2 else f1
        representativeToCcParent.addAll(newRep, representativeToCcParent.getImage(notNewRep))
        representativeToCcParent.remove(notNewRep)
    }

    override fun areEqual(e1: SmtExp, e2: SmtExp): Boolean {
        register(e1)
        register(e2)
        return uf.areEqual(e1, e2)
    }

    override fun toString(): String = uf.toString()

    override fun getEquivalenceClass(e: SmtExp): Set<SmtExp> {
        register(e)
        return uf.getEquivalenceClass(e)
    }
}

