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

class OneVarExpressionsTest : TACBuilderAuxiliaries() {

    /**
     * The example from the doc of [OneVarExpressions]
     */
    @Test
    fun basicTest() {
        val prog = TACProgramBuilder {
            b assign Add(cS, 3.asTACExpr)
            a assign Add(cS, 2.asTACExpr)
            d assign Mul(aS, bS)
            e assign Add(dS, dS, 3.asTACExpr)
            f assign Add(eS, eS)
        }
        assertEquals(
            setOf(e, d, c),
            OneVarExpressions(prog.code).go()[prog.block(0)]!![f]
        )
    }

    @Test
    fun reAssignment() {
        val prog = TACProgramBuilder {
            a assign Add(bS, 2.asTACExpr)
            b assign c
        }
        assertEquals(
            null,
            OneVarExpressions(prog.code).go()[prog.block(0)]!![a]
        )
    }

}
