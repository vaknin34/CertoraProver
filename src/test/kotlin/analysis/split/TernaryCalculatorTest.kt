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

package analysis.split

import datastructures.stdcollections.*
import evm.MAX_EVM_UINT256
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import vc.data.*
import java.math.BigInteger

class TernaryCalculatorTest : TACBuilderAuxiliaries() {

    private fun calculator(code: CoreTACProgram, highPrecision: Boolean) =
        TernaryCalculator(code, isForbiddenVar = { false }, highPrecision = highPrecision)

    /** if [highPrecision] is null then checks both. */
    private fun TACProgramBuilder.BuiltTACProgram.assertT(
        query: String,
        ternary: Ternary,
        highPrecision: Boolean? = null
    ) {
        val calculators = when (highPrecision) {
            false -> listOf(calculator(code, false))
            true -> listOf(calculator(code, true))
            null -> listOf(calculator(code, true), calculator(code, false))
        }
        val (ptr, cmd) = lcmd(query)
        check(cmd is TACCmd.Simple.AssigningCmd)
        for (c in calculators) {
            assertEquals(ternary, c.getLhs(ptr))
        }
    }

    @Test
    fun simple() {
        val prog = TACProgramBuilder {
            a assign BWAnd(cS, 0xf.asTACExpr) // so all zeros except unknown lower bits
            jump {
                jump(1) {
                    b assign BWAnd(dS, 0xf8.asTACExpr) // all zeros expect unknown in bits 3-8
                    label("query")
                    c assign BWAnd(aS, bS)
                }
            }
            jump {
                jump(1)
            }
        }
        // this means X (unknown) at the 3d bit exactly, and all else is 0.
        prog.assertT("query", Ternary(MAX_EVM_UINT256 - 8.toBigInteger(), BigInteger.ZERO))
    }

    @Test
    fun highPrecision() {
        val prog = TACProgramBuilder {

            jump {
                a assign SignExtend(1.asTACExpr, cS)
                jump(1) {
                    b assign SignExtend(1.asTACExpr, dS)
                    label("query")
                    c assign BWAnd(aS, bS)
                }
            }
            jump {
                a assign SignExtend(1.asTACExpr, eS)
                jump(1)
            }
        }
        // this means all bits are unknown, but we do know it is sign extended from bit 16.
        prog.assertT("query", Ternary(BigInteger.ZERO, BigInteger.ZERO, 16), highPrecision = true)
    }
}
