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

package vc.lexpression

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import smt.axiomgenerators.BasicConstantComputer
import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.TheoryFunctionSymbol
import tac.Tag
import vc.data.LExpression
import java.math.BigInteger

internal class LExpressionEvalKtTest {


    @Test
    fun test01() {
        Assertions.assertTrue(LExpression.Identifier("x", Tag.Bit256) ==
                LExpression.Identifier("x", Tag.Bit256))
        Assertions.assertFalse(LExpression.Identifier("x", Tag.Bit256) ==
                LExpression.Identifier("y", Tag.Bit256))
        Assertions.assertFalse(LExpression.Literal(BigInteger.ONE, Tag.Int) == LExpression.Literal(BigInteger.TWO, Tag.Int))
        Assertions.assertFalse((LExpression.Identifier("x", Tag.Bit256) as LExpression) ==
                LExpression.Literal(BigInteger.ONE, Tag.Int))
        Assertions.assertFalse((LExpression.Literal(false) as LExpression) ==
                (LExpression.Literal(BigInteger.ZERO, Tag.Int) as LExpression))

        val lExprFact = LExpressionFactory()
        val constantComputer = BasicConstantComputer(lExprFact)

        Assertions.assertEquals(
            LExpression.Literal(true),
            constantComputer.evalRec(
                LExpression.ApplyExpr(
                    TheoryFunctionSymbol.Binary.Eq(Tag.Int),
                    LExpression.Literal(BigInteger.TWO, Tag.Int),
                    LExpression.ApplyExpr(
                        TheoryFunctionSymbol.Vec.IntAdd,
                        LExpression.Literal(BigInteger.ONE, Tag.Int),
                        LExpression.Literal(BigInteger.ONE, Tag.Int),
                    ),
                )
            )
        )

    }


}

