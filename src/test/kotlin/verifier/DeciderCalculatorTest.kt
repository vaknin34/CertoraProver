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

package verifier

import analysis.LTACVar
import com.certora.collect.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import vc.data.TACSymbol
import vc.data.asTACExpr

class DeciderCalculatorTest : TACBuilderAuxiliaries() {

    private fun TACProgramBuilder.BuiltTACProgram.check(
        lhsQuery: String,
        vararg pairs: Pair<String, TACSymbol.Var>
    ) {
        val d = DeciderCalculator(code)
        d.go()
        val answer = d.lhsVal(ptr(lhsQuery))?.setOrNull
        val expected = pairs.map { LTACVar(ptr(it.first), it.second) }.toTreapSet()
        assertEquals(expected, answer)
    }


    private fun TACProgramBuilder.BuiltTACProgram.checkRhs(
        query: String,
        v : TACSymbol.Var,
        vararg pairs: Pair<String, TACSymbol.Var>
    ) {
        val d = DeciderCalculator(code)
        d.go()
        val answer = d.rhsVal(ptr(query), v).set
        val expected = pairs.map { LTACVar(ptr(it.first), it.second) }.toTreapSet()
        assertEquals(expected, answer)
    }


    @Test
    fun test1() {
        val prog = TACProgramBuilder {
            label("0")
            b assign Add(aS, 2.asTACExpr)
            label("1")
            c assign Add(bS, 2.asTACExpr)
            label("query")
            d assign Mul(cS, 3.asTACExpr)
        }
        prog.check(
            "query",
            "0" to a, "1" to b, "query" to c
        )
    }

    @Test
    fun test2() {
        val prog = TACProgramBuilder {
            label("0")
            a assign Add(bS, 2.asTACExpr)
            label("query")
            c assign Mul(aS, 3.asTACExpr, bS)
        }
        prog.check(
            "query",
            "0" to b
        )
    }

    @Test
    fun test3() {
        val prog = TACProgramBuilder {
            label("0")
            b assign Add(aS, 2.asTACExpr)
            jump(1) {
                label("1")
                c assign Mul(4.asTACExpr, bS)
                label("2")
                d assign Add(5.asTACExpr, cS)
                label("query")
                f assign Mul(dS, eS)
            }
        }
        prog.checkRhs(
            "query",
            d,
            "2" to c,
            "1" to b,
            "0" to a,
            "query" to d
        )
    }

    @Test
    fun test4() {
        val prog = TACProgramBuilder {
            label("query")
            b assign ShiftRightLogical(0x10.asTACExpr, aS)
        }
        prog.checkRhs(
            "query",
            a,
            "query" to a
        )
    }
}
