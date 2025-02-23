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

package analysis.dataflow

import analysis.dataflow.StrictDefAnalysis.Source
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import vc.data.TACSymbol

class StrictDefAnalysisTest : TACBuilderAuxiliaries() {


    /** asserts that [v] at [queryPoint] (block to pos) has the def site of [expected] */
    private fun TACProgramBuilder.BuiltTACProgram.assertDef(
        v: TACSymbol.Var,
        queryPoint: String = "query",
        vararg expected: String?
    ) {
        val def = code.analysisCache.strictDef
        assertEquals(
            expected.map { it?.let { ptr(it) } }.toSet(),
            def.defSitesOf(v, ptr(queryPoint)).toSet()
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
        prog.assertDef(a, "query", "def")
    }

    @Test
    fun simpleDiamond2() {
        val prog = TACProgramBuilder {
            label("def1")
            a assign 1
            jump {
                label("def2")
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
        prog.assertDef(a, "query", "def1", "def2")
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
        prog.assertDef(a, "query", "def")
    }

    @Test
    fun loop2() {
        val prog = TACProgramBuilder {
            label("def1")
            a assign 1
            jump(1) {
                label("query")
                nop
                label("def2")
                a assign 2
                jump(1)
            }
        }
        prog.assertDef(a, "query", "def1", "def2")
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
        prog.assertDef(a, "query", "def")
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
        prog.assertDef(a, "query", "def")
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
        prog.assertDef(a, "query", "def")
    }

    @Test
    fun multiple() {
        val prog = TACProgramBuilder {
            jump(1) {
                label("def1")
                a assign 1
                jump(3) {
                    jump(4) {
                        label("query")
                        nop
                    }
                }
            }
            jump(2) {
                label("def2")
                a assign 2
                jump(3)
            }
        }
        prog.assertDef(a, "query", "def1", "def2")
    }

    @Test
    fun multipleWithHavoc() {
        val prog = TACProgramBuilder {
            jump(1) {
                label("def1")
                a assign 1
                jump(3) {
                    label("query")
                    nop
                }
            }
            jump(2) {
                jump(3)
            }
        }
        prog.assertDef(a, "query", "def1", null)
    }

    @Test
    fun fallback() {
        val prog = TACProgramBuilder {
            label("def1")
            a assign 1
            jump(1) {
                jump(3) {
                    label("query")
                    nop
                }
            }
            jump(2) {
                label("def2")
                a assign 2
                jump(3)
            }
        }
        prog.assertDef(a, "query", "def1", "def2")
    }


    /** asserts that [v] at [queryPoint] (block to pos) has the def site of [expected] */
    private fun TACProgramBuilder.BuiltTACProgram.assertSource(
        v: TACSymbol,
        expected: Source,
        queryPoint: String = "query"
    ) {
        val def = code.analysisCache.strictDef
        assertEquals(
            expected,
            def.source(ptr(queryPoint), v)
        )
    }

    @Test
    fun source1() {
        val prog = TACProgramBuilder {
            label("source")
            c assign Add(dS, One)
            b assign c
            label("query")
            a assign b
        }
        prog.assertSource(b, Source.Defs(prog.ptr("source")))
    }

    @Test
    fun source2() {
        val prog = TACProgramBuilder {
            c assign d
            b assign c
            label("query")
            a assign b
        }
        prog.assertSource(b, Source.Uinitialized(d))
    }

    @Test
    fun source3() {
        val prog = TACProgramBuilder {
            jump(1) {
                label("source")
                c assign 7
                jump(3) {
                    b assign c
                    label("query")
                    a assign b
                }
            }
            jump(2) {
                jump(3)
            }

        }
        prog.assertSource(b, Source.Defs(prog.ptr("source"), null))
    }

    @Test
    fun source4() {
        val prog = TACProgramBuilder {
            jump(1) {
                c assign 7
                b assign c
                label("query")
                a assign b
            }
        }
        prog.assertSource(b, Source.Const(7.toBigInteger()))
    }

    @Test
    fun source5() {
        val prog = TACProgramBuilder {
            jump(1) {
                c assign 7
                b assign c
                label("query")
                a assign e
            }
        }
        prog.assertSource(e, Source.Uinitialized(e))
    }
}
