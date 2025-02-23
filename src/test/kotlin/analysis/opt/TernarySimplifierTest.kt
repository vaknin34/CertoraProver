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

package analysis.opt

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import vc.data.TACProgramBuilder.Companion.testProgString
import vc.data.asTACExpr

class TernarySimplifierTest : TACBuilderAuxiliaries() {

    @Test
    fun testSimplifyMask() {
        val prog = TACProgramBuilder {
            b assign Mul(aS, 16.asTACExpr)
            c assign BWAnd(bS, 0xffff0.asTACExpr)
        }
        val expected = TACProgramBuilder {
            b assign Mul(aS, 16.asTACExpr)
            c assign BWAnd(bS, 0xfffff.asTACExpr)
        }
        val simplified = TernarySimplifier.simplify(prog.code, false)
        assertEquals(
            testProgString(expected.code),
            testProgString(simplified)
        )
    }

    /** See the simplification doesn't happen when it shouldn't */
    @Test
    fun testSimplifyMaskSanity() {
        val prog = TACProgramBuilder {
            b assign Mul(aS, 8.asTACExpr)
            c assign BWAnd(bS, 0xffff0.asTACExpr)
        }
        val simplified = TernarySimplifier.simplify(prog.code, false)
        assertEquals(
            testProgString(prog.code),
            testProgString(simplified)
        )
    }

}
