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

import evm.EVM_BITWIDTH256
import utils.foldFirst
import utils.monadicMap
import vc.data.TACExpr
import java.math.BigInteger

/**
 * A linear term, representing the *syntactic* construction r1 * v1 + r2 * v2 + ... rn * vn + k
 *
 * The vi in the above are not necessarily unique. Until this [LinearTerm] is lifted into a [LinearEquality]
 * it has no semantic meaning. In practice, it is expected these instances are only created during the DSL building
 * operations; if you ever think you want an explicit reference to a [LinearTerm] you almost certainly want a [LinearEquality].
 *
 * [terms] represents the sequence r1 * v1 + ... in the above and [k] represents the (unique) BigInteger number [k].
 * [terms] is *not* an association list, a variable v may appear multiple times; linear terms are combined by
 * simple list concatenation, the equivalent of conjoining two formulae without simplification.
 *
 * In the following we denote by [[this]] the syntactic formula represented by this object
 */
data class LinearTerm(val terms: List<LinearAtom>, val k: BigInteger = BigInteger.ZERO) {
    /**
     * DSL operation: yield the [LinearTerm] representing [[this]] + -1 * [[v]]
     */
    operator fun minus(v: LVar) = this + (v to BigInteger.ONE.negate())

    /**
     * DSL operation: yield the [LinearTerm] representing [[this]] - [v]
     */
    operator fun minus(v: LinearAtom) = this.copy(
        terms = this.terms + (v.first to v.second.negate())
    )

    /**
     * DSL operation: yield the [LinearTerm] representing [[this]] - [v]
     */
    operator fun minus(v: LinearTerm) =
        this.copy(terms = this.terms + v.terms.map { it.first to it.second.negate() }, k = this.k + v.k.negate())

    /**
     * DSL operation: yield the [LinearTerm] representing [[this]] + -1 * [l]
     */
    operator fun plus(l: LVar) = l + this

    /**
     * DSL operation: yield the [LinearTerm] representing [[this]] + [a]
     */
    operator fun plus(a: LinearAtom) = this.copy(terms = this.terms + a)

    /**
     * DSL Operation: yield the [LinearTerm] representing [[this]] + [[t]]
     */
    operator fun plus(t: LinearTerm) = this.copy(terms = this.terms + t.terms, k = this.k + t.k)

    /**
     * DSL Operation: yield the [LinearTerm] representing [[this]] + [r]
     */
    operator fun plus(n: BigInteger) = this.copy(k = this.k + n)

    /**
     * DSL Operation: yield the [LinearTerm] representing [[this]] + [n]
     */
//    operator fun plus(n: BigInteger) = this + n

    /**
     * DSL Operation: yield the [LinearTerm] representing [[this]] + [k]
     */
    operator fun plus(k: Int) = this + k.toBigInteger()

    operator fun times(k: BigInteger) = LinearTerm(
        this.terms.map {
            it.first to (it.second * k)
        },
        k = this.k * k
    )

    operator fun times(n: Int) = this * n.toBigInteger()

    companion object {
        fun lift(p: TACExpr): LinearTerm? =
            lift(p, BigInteger.ONE)

        private fun lift(p: TACExpr, coeff: BigInteger): LinearTerm? {
            return when (p) {
                is TACExpr.Vec.Mul -> {
                    if (p.ls.size != 2) {
                        return null
                    }
                    val x = p.o1
                    val y = p.o2
                    when {
                        x is TACExpr.Sym.Const -> {
                            lift(y, x.s.value * coeff)
                        }
                        y is TACExpr.Sym.Const -> {
                            lift(x, y.s.value * coeff)
                        }
                        else -> null
                    }
                }
                is TACExpr.Vec.Add -> {
                    p.ls.monadicMap { lift(it, coeff) }?.foldFirst { a, b -> a + b }
                }
                is TACExpr.BinOp.Sub -> {
                    lift(p.o1, coeff)?.let { a1 ->
                        lift(p.o2, coeff.negate())?.let { a2 ->
                            a1 + a2
                        }
                    }
                }
                is TACExpr.Sym.Const -> LinearTerm(listOf(), p.s.value * coeff)
                is TACExpr.Sym.Var -> LinearTerm(listOf(LinearAtom(LVar.PVar(p.s), coeff)))
                is TACExpr.BinOp.ShiftLeft -> {
                    if(p.o2 is TACExpr.Sym.Const && p.o2.s.value < EVM_BITWIDTH256.toBigInteger()) {
                        lift(p.o1, BigInteger.TWO.pow(p.o2.s.value.intValueExact()))
                    } else {
                        null
                    }
                }
                else -> null
            }
        }
    }
}