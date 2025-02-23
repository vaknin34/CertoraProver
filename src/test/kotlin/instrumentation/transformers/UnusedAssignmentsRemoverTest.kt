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

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import vc.data.TACCmd
import vc.data.TACProgramBuilder
import vc.data.TACProgramBuilder.BuiltTACProgram
import vc.data.TACProgramBuilder.Companion.testProgString

@Suppress("unused")
class UnusedAssignmentsRemoverTest : TACBuilderAuxiliaries() {

    private fun runAndCompare(original: BuiltTACProgram, expected: BuiltTACProgram, expensive: Boolean) {
        val newProg =
            removeUnusedAssignments(original.code, expensive = expensive, isErasable = { true }, isTypechecked = true)
        assertEquals(testProgString(expected.code), testProgString(newProg))
    }

    @Test
    fun test1() {
        val originalProg = TACProgramBuilder {
            x assign y
            jump {
                y assign z
            }
        }
        val expectedProg = TACProgramBuilder {
            jump {
                nop
            }
        }
        runAndCompare(originalProg, expectedProg, expensive = false)
        runAndCompare(originalProg, expectedProg, expensive = true)
    }

    @Test
    fun test2() {
        val originalProg = TACProgramBuilder {
            b assign c
            a assign b
            jump {
                a assign c
                x assign Lt(aS, bS)
                assert(x)
            }
        }
        val expectedProg = TACProgramBuilder {
            b assign c
            jump {
                a assign c
                x assign Lt(aS, bS)
                assert(x)
            }
        }
        runAndCompare(originalProg, expectedProg, expensive = true)
        runAndCompare(originalProg, expectedProg, expensive = false)
    }

    @Test
    fun testLoop() {
        val originalProg = TACProgramBuilder {
            a assign 1
            jump(1) {
                x assign Gt(aS, Zero)
                jump(2) {
                    a assign 2
                    assert(x)
                    jump(1)
                }
            }
            jump(2)
        }
        runAndCompare(originalProg, originalProg, expensive = false)
    }


    @Test
    fun test3() {
        val originalProg = TACProgramBuilder {
            a assign 1
            x assign (aS eq bS)
            jumpCond(x)
            jump {
                c assign d
                jump(1) {
                    d assign Mul(cS, cS)
                    assert(x)
                }
            }
            jump {
                a assign 2
                jump(1)
            }
        }
        val expectedProg = TACProgramBuilder {
            a assign 1
            x assign (aS eq bS)
            jumpCond(x)
            jump {
                jump(1) {
                    assert(x)
                }
            }
            jump {
                jump(1)
            }
        }

        runAndCompare(originalProg, expectedProg, expensive = false)
    }


    @Test
    fun testLogIsNotSink() {
        val originalProg = TACProgramBuilder {
            a assign 1
            addCmd(TACCmd.Simple.LogCmd(listOf(a)))
        }
        val expectedProg = TACProgramBuilder {
            addCmd(TACCmd.Simple.LogCmd(listOf(a)))
        }
        runAndCompare(originalProg, expectedProg, expensive = false)
    }


    @Test
    fun testCheapWithLoop() {
        val originalProg = TACProgramBuilder {
            jump(1) {
                z assign Eq(yS, True)
                x assign y
                y assign Eq(xS, True)
                z assign y
                jump(1)
                jump(2) {
                    assert(x)
                }
            }
        }
        val expectedProg = TACProgramBuilder {
            jump(1) {
                x assign y
                y assign Eq(xS, True)
                jump(1)
                jump(2) {
                    assert(x)
                }
            }
        }
        runAndCompare(originalProg, expectedProg, expensive = true)
    }

}
