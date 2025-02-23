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

import analysis.opt.inliner.GlobalInliner.Companion.inlineStats
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import vc.data.asTACExpr

class GlobalInlinerTest : TACBuilderAuxiliaries() {

    private fun TACProgramBuilder.BuiltTACProgram.checkStats(vararg pairs: Pair<String, Int>) {
        val stats = inlineStats(code)
        val expected = buildMap {
            for ((str, count) in pairs) {
                this[str] = count
            }
        }
        Assertions.assertEquals(expected, stats.toMap())
    }


    @Test
    fun writeRead() {
        val prog = TACProgramBuilder {
            bMap1[32] assign a
            b assign bMap1[32]
        }
        prog.checkStats("byteLoad" to 1)
    }

    @Test
    fun constant() {
        val prog = TACProgramBuilder {
            b assign Add(aS, 3.asTACExpr)
            c assign Sub(bS, aS)
        }
        prog.checkStats("constant" to 1)
    }

    @Test
    fun constant2() {
        val prog = TACProgramBuilder {
            b assign Add(aS, 3.asTACExpr)
            bMap1[b] assign b
            c assign bMap1[b]
            d assign Sub(cS, aS)
        }
        prog.checkStats("byteLoad" to 1, "constant" to 1)
    }


    @Test
    fun simpleVar() {
        val prog = TACProgramBuilder {
            b assign Add(aS, 3.asTACExpr)
            c assign Sub(bS, 3.asTACExpr)
        }
        prog.checkStats("simpleVar" to 1)
    }

    @Test
    fun complex() {
        val prog = TACProgramBuilder {
            b assign Add(aS, 3.asTACExpr)
            bMap1[10] assign b
            e assign bMap1[10]
        }
        prog.checkStats("byteLoad" to 1)
    }

    @Test
    fun missed() {
        val prog = TACProgramBuilder {
            b assign Add(aS, 3.asTACExpr)
            d assign Add(bS, cS)
            bMap1[10] assign d
            e assign bMap1[10]
        }
        prog.checkStats("missedByteLoad" to 1)
    }
}
