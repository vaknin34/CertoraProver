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
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import vc.data.TACProgramBuilder.BuiltTACProgram
import vc.data.TACSymbol

internal class DefiniteDefSitesTest : TACBuilderAuxiliaries() {

    /** asserts that [v] at [queryPoint] (block to pos) has the def site of [expected] */
    private fun BuiltTACProgram.assertDef(v: TACSymbol.Var, queryPoint: String = "query", expected: String? = "def") {
        val def = DefiniteDefSites(code)
        assertEquals(
            expected?.let { ptr(expected) },
            def.getDefinitiveDef(ptr(queryPoint), v)
        )
    }

    @Test
    fun defAfter() {
        val prog = TACProgramBuilder {
            b assign 10
            label("def")
            a assign 1
            label("query")
            a assign 3
        }
        prog.assertDef(a, "query", "def")
        prog.assertDef(a, "def", null)
    }


    @Test
    fun simpleDiamond() {
        val prog = TACProgramBuilder {
            label("def")
            a assign 1
            jump {
                jump(3) {
                    label("query")
                    nop
                }
            }
            jump {
                jump(3)
            }
        }
        prog.assertDef(a)
    }

    @Test
    fun simpleDiamond2() {
        val prog = TACProgramBuilder {
            a assign 1
            jump {
                a assign 2
                jump(3) {
                    label("query")
                    a assign 3
                }
            }
            jump {
                jump(3)
            }
        }
        prog.assertDef(a, "query", null)
    }

    @Test
    fun loop1() {
        val prog = TACProgramBuilder {
            label("def")
            a assign 1
            jump(1) {
                jump(2) {
                    label("query")
                    jump(3) {
                        a assign 3
                    }
                }
                jump(1)
            }
        }
        prog.assertDef(a)
    }

    @Test
    fun loop2() {
        val prog = TACProgramBuilder {
            a assign 1
            jump(1) {
                label("query")
                nop
                a assign 2
                jump(1)
            }
        }
        prog.assertDef(a, "query", null)
    }

    @Test
    fun twoDominatingPlusOneNot() {
        val prog = TACProgramBuilder {
            a assign 1
            jump(1) {
                label("def")
                a assign 2
                jump(2) {
                    jump(3) {
                        label("query")
                        nop
                    }
                    jump(4) {
                        a assign 7
                    }
                }
                jump(3)
            }
        }
        prog.assertDef(a)
    }

    @Test
    fun cycleCheck() {
        val prog = TACProgramBuilder {
            label("def")
            a assign 1
            jump(1) {
                jump(2) {
                    jump(1)
                    jump(4) {
                        label("query")
                        nop
                    }
                }
                jump(3) {
                    a assign 2
                }
            }
        }
        prog.assertDef(a)
    }

    @Test
    fun havocCheck() {
        val prog = TACProgramBuilder {
            a assign 1
            label("def")
            havoc(a)
            jump(1) {
                label("query")
                nop
            }
        }
        prog.assertDef(a)
    }

}
