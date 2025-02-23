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

package analysis.opt.intervals

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import vc.data.asTACExpr

class IntervalsOfExpressionTest  : TACBuilderAuxiliaries() {

    @Test
    fun test0() {
        val prog = TACProgramBuilder {
            z assign Lt(aS, 10.asTACExpr)
            label("query")
            assume(z)
        }
        assertEquals(
            Intervals(0, 9),
            intervalsOfOneVarExpression(prog.code, prog.ptr("query"), zS, a)
        )
    }


    @Test
    fun overflowTest1() {
        val prog = TACProgramBuilder {
            b assign Mul(aS, 10.asTACExpr)
            c assign BWAnd(bS, 0xff.asTACExpr)
            d assign Div(cS, aS)
            z assign Eq(dS, 10.asTACExpr)
            label("query")
            assume(z)
        }
        assertEquals(
            Intervals(1, 25),
            intervalsOfOneVarExpression(prog.code, prog.ptr("query"), zS, a, Intervals(1, 10000))
        )
    }

    @Test
    fun overflowTest2() {
        val prog = TACProgramBuilder {
            b assign Mul(aS, 10.asTACExpr)
            c assign BWAnd(bS, 0xff.asTACExpr)
            d assign Div(cS, aS)
            x assign Eq(dS, 10.asTACExpr)
            y assign Eq(aS, 0.asTACExpr)
            z assign LOr(xS, yS)
            label("query")
            assume(z)
        }
        assertEquals(
            Intervals(0, 25),
            intervalsOfOneVarExpression(prog.code, prog.ptr("query"), zS, a)
        )
    }

}
