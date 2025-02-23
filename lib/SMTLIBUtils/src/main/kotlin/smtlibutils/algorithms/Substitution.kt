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
import smtlibutils.data.SmtExp
import utils.*
import java.lang.IllegalArgumentException


/**
 * Semantics: Applying this substitution to an [SmtExp] e _simultaneously_ replaces all variables in e that are in the
 * [domain] of this substitution expressions according to [map].
 */
data class SmtExpSubstitution private constructor(private val map: Map<SmtExp.QualIdentifier, SmtExp>) {

    private val substitutor by lazy {
        Substitutor(map.mapKeys {
            it.key
        })
    }

    /**
     * Returns as substitution that simultaneously applies [this] and substitutes [l] by [r].
     * Will crash if the domain of [this] contains [l].
     */
    fun appendParallel(l: SmtExp.QualIdentifier, r: SmtExp): SmtExpSubstitution {
        check(l.sort == r.sort)
        return this.composeParallel(SmtExpSubstitution(mapOf(l to r)))
    }

    /**
     * Returns as substitution that simultaneously applies [this] and [other].
     * Will crash if the domains of [this] and [other] intersect.
     */
    fun composeParallel(other: SmtExpSubstitution): SmtExpSubstitution {
        check(!this.domain().containsAny(other.domain())) {
            throw IllegalArgumentException("domains not disjoint, unexpected, may need to revise")
        }
        return SmtExpSubstitution(this.map + other.map)
    }

    /**
     * Returns a substitution that first substitutes everything according to [this], and then substitutes [l] by [r].
     *
     * Note: could be optimized.
     */
    fun append(l: SmtExp.QualIdentifier, r: SmtExp): SmtExpSubstitution =
        this.compose(SmtExpSubstitution(mapOf(l to r)))

    /**
     * Returns a substitution that has the same effect as first applying [this] and then [other].
     */
    fun compose(other: SmtExpSubstitution): SmtExpSubstitution {
        val newMap = mutableMapOf<SmtExp.QualIdentifier, SmtExp>()
        /* transform the expressions that are already in the image according to [other] */
        newMap.putAll(this.map.mapValues { other.applyTo(it.value) })
        /* add all pairs where [this] does nothing as they occur in [other] */
        other.domain().forEach {
            if (it !in this.domain())
                newMap[it] = other.map[it] ?: error("domain() function is inconsistent")
        }
        return SmtExpSubstitution(newMap)
    }

    fun composeIfCompatible(other: SmtExpSubstitution, eGraph: EquivalenceRelation<SmtExp>): SmtExpSubstitution? =
        if (!this.domain().containsAny(other.domain())) {
            this.composeParallel(other)
        } else if (!this.map.entries.any { (key, value) ->
                val otherVal = other.map[key]
                otherVal != null && !eGraph.areEqual(otherVal, value)
            }) {
            this.compose(other)
        } else
            null // substitutions aren't independent


    fun domain(): Set<SmtExp.QualIdentifier> = map.keys

    fun applyTo(x: SmtExp): SmtExp = substitutor.expr(x, Unit)

    override fun toString(): String {
        return map.entries
            .map { (key, value) -> "$key -> $value" }
            .joinToString(separator = ", ", prefix = "[", postfix = "]")
    }

    companion object {
        val Empty = SmtExpSubstitution(mapOf())
    }
}
