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

import vc.data.TACSymbol
import java.math.BigInteger

/**
 * A linear variable.
 */
sealed class LVar {
    /**
     * A program variable, embeds [TACSymbol.Var]
     */
    data class PVar(val v: TACSymbol.Var) : LVar()

    /**
     * A synthetic variable, tracking some ghost state (i.e., the length of some array block, the number
     * of bytes reads so far, etc.)
     */
    data class Instrumentation(val id: String) : LVar()


    /**
     * DSL operation: return the [LinearAtom] representing [this] * [n]
     */
    operator fun times(n: BigInteger) : LinearAtom = this to n

    /**
     * DSL Operation: return the [LinearAtom] representing [this] * [n]
     */
    operator fun times(n: Int) : LinearAtom = this * n.toBigInteger()

    /**
     * DSL Operation: return the [LinearTerm] representing 1 * [this] + 1 * [q]
     */
    operator fun plus(q: LVar) = scaleByOne() + q.scaleByOne()

    /**
     * DSL Operation: Return the [LinearTerm] representing 1 * [this] + [t]
     */
    operator fun plus(t: LinearTerm) = scaleByOne() + t

    /**
     * DSL Operation: Return the [LinearTerm] representing 1 * [this] + [a]
     */
    operator fun plus(a: LinearAtom) = scaleByOne() + a

    /**
     * DSL Operation: Return the linear term representing 1 * [this] + [k]
     */
    operator fun plus(k: Int) = this + k.toBigInteger()


    /**
     * DSL Operation: Return the linear term representing 1 * [this] + [r]
     */
    operator fun plus(r: BigInteger) = LinearTerm(terms = listOf(this to BigInteger.ONE), k = r)


    /**
     * DSL Operation: Return the linear term representing 1 * [this] - [a]
     */
    operator fun minus(a: LinearAtom) = scaleByOne() - a

    /**
     * DSL Operation: Return the linear term representing 1 * [this] + -1 * [l]
     */
    operator fun minus(l: LVar) = scaleByOne() - l.scaleByOne()

    /**
     * DSL Operation: return the linear term representing 1 * [this] - [t]
     */
    operator fun minus(t: LinearTerm) = scaleByOne() - t

    private fun scaleByOne() = this.times(BigInteger.ONE)
    operator fun plus(symbol: TACSymbol) = when(symbol) {
        is TACSymbol.Const -> this + symbol.value
        is TACSymbol.Var -> this + PVar(symbol)
    }
}