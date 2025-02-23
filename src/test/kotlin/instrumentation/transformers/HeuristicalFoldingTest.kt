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

package instrumentation.transformers

import instrumentation.transformers.PeepHoleOptimizer.peepHoleOptimizeExprMapper
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import tac.StartBlock
import tac.Tag
import vc.data.*

internal class HeuristicalFoldingTest {

    val txf = TACExprFactTypeCheckedOnlyPrimitives

    @Test
    fun peepHoleIte01() {
        val resultExp = peepHoleOptimizeExprMapper.transformOuter(txf {
            Ite(
                bool(true),
                number(3),
                Mul(number(4), number(5))
            )
        })
        assertEquals(
            TACSymbol.lift(3).asSym(),
            resultExp
        )
    }

    @Test
    fun peepHoleIte02() {
        val resultExp = peepHoleOptimizeExprMapper.transformOuter(txf {
            Ite(
                bool(false),
                number(3),
                Mul(number(4), number(5))
            )
        })
        assertEquals(
            TACSymbol.lift(20).asSym(),
            resultExp
        )
    }

    @Test
    fun peepHoleArith01() {
        val resultExp = peepHoleOptimizeExprMapper.transformOuter(txf {
            Add(
                number(3),
                Mul(number(4), number(5))
            )
        })
        assertEquals(
            TACSymbol.lift(23).asSym(),
            resultExp
        )
    }

    @Test
    fun peepHoleArith02() {
        val x = TACSymbol.Var("x", Tag.Bit256).asSym()
        val resultExp = peepHoleOptimizeExprMapper.transformOuter(txf {
            Add(
                number(3),
                Mul(number(4), number(5), x)
            )
        })
        val expected = txf {
            Add(
                number(3),
                Mul(number(20), x)
            )
        }
        assertTrue(expected.equalIgnoreTypes(resultExp))
        assertEquals(expected, resultExp) // this even works, but the previous line would be fine for this test as well
    }

    /**
     * Structurally compares two [TACExpr]s, ignores [TACExprTag].
     * (Can be useful for testing when you don't want to have to ensure that a self-built expression is tagged the same
     *  way as the one the tested function produces.)
     */
    infix fun TACExpr.equalIgnoreTypes(other: TACExpr): Boolean {
        if (this == other) {
            return true
        }
        if (this::class != other::class) {
            return false
        }
        // at this point we know the classes match, so the casts below are safe

        return when (this) {
            is TACExpr.Apply -> {
                other as TACExpr.Apply
                this.f == other.f && this.ops.zip(other.ops).all { (l, r) -> l.equalIgnoreTypes(r) }
            }

            is TACExpr.BinBoolOp -> {
                other as TACExpr.BinBoolOp
                this.ls.zip(other.ls).all { (l, r) -> l.equalIgnoreTypes(r) }
            }

            is TACExpr.BinOp -> {
                other as TACExpr.BinOp
                this.o1.equalIgnoreTypes(other.o1) && this.o2.equalIgnoreTypes(other.o2)
            }

            is TACExpr.BinRel -> {
                other as TACExpr.BinRel
                this.o1.equalIgnoreTypes(other.o1) && this.o2.equalIgnoreTypes(other.o2)
            }

            is TACExpr.Sym.Const -> {
                other as TACExpr.Sym.Const
                this.s.value == other.s.value
            }

            is TACExpr.Sym.Var -> {
                other as TACExpr.Sym.Var
                this.s.smtRep == other.s.smtRep
            }

            is TACExpr.TernaryExp.Ite -> {
                other as TACExpr.TernaryExp.Ite
                this.i.equalIgnoreTypes(other.i) && this.t.equalIgnoreTypes(other.t) && this.e.equalIgnoreTypes(other.e)
            }

            is TACExpr.UnaryExp -> {
                other as TACExpr.UnaryExp
                this.o.equalIgnoreTypes(other.o)
            }

            is TACExpr.Vec -> {
                other as TACExpr.Vec
                this.ls.zip(other.ls).all { (l, r) -> l.equalIgnoreTypes(r) }
            }

            else -> error("function `equalIgnoreTypes` is not yet implemented for this case (${this::class})")
        }
    }
}
