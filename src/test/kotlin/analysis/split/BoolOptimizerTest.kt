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

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import tac.Tag
import vc.data.CoreTACProgram
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import vc.data.TACProgramBuilder.BuiltTACProgram
import vc.data.TACProgramBuilder.Companion.testProgString
import vc.data.tacexprutil.CmdsFolder
import vc.data.withDestructiveOptimizations

class BoolOptimizerTest : TACBuilderAuxiliaries() {

    private fun assertSameProg(expected: CoreTACProgram, resulting: CoreTACProgram) {
        assertEquals(
            testProgString(expected),
            testProgString(resulting)
        )
    }

    private fun runAndCompare(expected: BuiltTACProgram, original: BuiltTACProgram) {
        val newProg = BoolOptimizer(original.code.withDestructiveOptimizations(true)).go()
        assertSameProg(expected.code.withDestructiveOptimizations(true), newProg)
    }

    /** Fold to one expression, because we want to ignore the names of the temp vars the optimizer generates. */
    private fun runAndCompareAsExpr(expected: BuiltTACProgram, original: BuiltTACProgram, blockExpected : Int = 0, blockOriginal : Int = 0) {
        val resProg = BoolOptimizer(original.code).go()
        assertEquals(
            CmdsFolder.fold(expected.code, xS, original.block(blockExpected)),
            CmdsFolder.fold(resProg, xS, original.block(blockOriginal))
        )
    }

    private val boolA = BoolOptimizer.boolify(a)
    private val boolC = BoolOptimizer.boolify(c)

    @Test
    fun test1() {
        val prog = TACProgramBuilder {
            x assign z
            a assign Ite(xS, One, Zero)
            y assign Eq(aS, Zero)
            assert(y)
        }
        val expected = TACProgramBuilder {
            x assign z
            boolA assign Ite(xS, True, False)
            y assign Eq(boolA.asSym(), False)
            assert(y)
        }
        runAndCompare(expected, prog)
    }

    @Test
    fun test2() {
        val prog = TACProgramBuilder {
            x assign Lt(aS, bS)
            assert(x)
        }
        runAndCompare(prog, prog)
    }

    @Test
    fun test3() {
        val prog = TACProgramBuilder {
            x assign Lt(Zero, One)
            assert(x)
        }
        val expected = TACProgramBuilder {
            x assign LAnd(LNot(False), True)
            assert(x)
        }
        runAndCompareAsExpr(expected, prog)
    }

    @Test
    fun test4() {
        val prog = TACProgramBuilder {
            jump(1) {
                a assign Ite(xS, One, Zero)
                jump(3) {
                    y assign Eq(aS, Zero)
                    assert(y)
                }
            }
            jump(2) {
                c assign Ite(yS, Zero, One)
                a assign c
                jump(3)
            }
        }

        val expected = TACProgramBuilder {
            jump(1) {
                boolA assign Ite(xS, True, False)
                jump(3) {
                    y assign Eq(boolA.asSym(), False)
                    assert(y)
                }
            }
            jump(2) {
                boolC assign Ite(yS, False, True)
                boolA assign boolC.asSym()
                jump(3)
            }
        }
        runAndCompare(expected, prog)
    }

    @Test
    fun test5() {
        val prog = TACProgramBuilder {
            jump(1) {
                c assign One
                jump(3) {
                    b assign Mul(cS, aS)
                    x assign Eq(bS, Zero)
                    assert(x)
                }
            }
            jump(2) {
                c assign Zero
                jump(3)
            }
        }
        val expected = TACProgramBuilder {
            b assign Ite(boolC.asSym(), aS, Zero)
            x assign Eq(bS, Zero)
            assert(x)
        }
        runAndCompareAsExpr(expected, prog, blockOriginal = 3)
    }

    @Test
    fun test6() {
        val prog = TACProgramBuilder {
            a assign Ite(yS, Zero, One)
            c assign Ite(
                Eq(safeMathNarrow(IntSub(One, aS), Tag.Bit256), One),
                One,
                Zero
            )
            x assign Eq(cS, Zero)
            assert(x)
        }
        val expected = TACProgramBuilder {
            boolA assign Ite(yS, False, True)
            boolC assign Ite(
                Eq(LNot(boolA.asSym()), True),
                True,
                False
            )
            x assign Eq(boolC.asSym(), False)
            assert(x)
        }
        runAndCompareAsExpr(expected, prog)
    }
}
