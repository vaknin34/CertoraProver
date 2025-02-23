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

package analysis.numeric.linear

import java.math.BigInteger

/**
 * A linear atom, consisting of a linear variable [LVar] scaled by an integer [BigInteger]
 */
typealias LinearAtom = Pair<LVar, BigInteger>

/**
 * DSL Operation: create a [LinearTerm] representing the addition of this linear atom added to [v]
 */
operator fun LinearAtom.plus(v: LinearAtom) = LinearTerm(listOf(this, v))

/**
 * DSL Operation: create a [LinearTerm] representing the addition of this linear atom added to [v]
 */
operator fun LinearAtom.plus(v: LinearTerm) = v + this

/**
 * DSL Operation: create a [LinearTerm] representing the addition of this linear atom to 1 * [v]
 */
operator fun LinearAtom.plus(v: LVar) = v + this

/**
 * DSL Operation: create a [LinearTerm] representing the addition of the constant [v] to this atom
 */
operator fun LinearAtom.plus(v: Int) = this + v.toBigInteger()


/**
 * DSL Operation: create a [LinearTerm] representing the addition of the constant [v] to this atom
 */
operator fun LinearAtom.plus(v: BigInteger) = LinearTerm(terms = listOf(this), k = v)

/**
 * DSL Operation: create a [LinearTerm] representing the addition of this linear term to -1 * [v]
 */
operator fun LinearAtom.minus(v: LVar) = listOf(
        this,
        v to BigInteger.ONE.negate()
)

/**
 * DSL Operation: create a [LinearTerm] representing the subtraction of the [LinearAtom] [v] from this
 */
operator fun LinearAtom.minus(v: LinearAtom) = LinearTerm(listOf(
        this,
        v.first to v.second.negate()
))

/**
 * DSL Operation: create a [LinearTerm] representing the subtraction of the [LinearTerm] [v] from this
 */
operator fun LinearAtom.minus(v: LinearTerm) = LinearTerm(
        terms = v.terms.map { (k,r) -> k to r.negate() } + this,
        k = v.k.negate()
)
