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

import analysis.assertNotNull
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import vc.data.CoreTACProgram
import vc.data.TACBuilderAuxiliaries
import vc.data.TACCmd
import vc.data.TACProgramBuilder
import vc.data.TACProgramBuilder.BuiltTACProgram
import vc.data.TACProgramBuilder.Companion.testProgString
import vc.data.tacexprutil.CmdsFolder
import vc.data.tacexprutil.ExprUnfolder.Companion.type

class NegationNormalizerTest  : TACBuilderAuxiliaries() {

    private fun assertSameProg(expected: CoreTACProgram, resulting: CoreTACProgram) {
        assertEquals(
            testProgString(expected),
            testProgString(resulting)
        )
    }

    private fun runAndCompare(expected: BuiltTACProgram, original: BuiltTACProgram) {
        val newProg = NegationNormalizer(original.code).rewrite()
        assertSameProg(expected.code, newProg)
    }

    @Test
    fun normalize1() {
        val prog = TACProgramBuilder {
            x assign LNot(yS)
            z assign LNot(xS)
        }
        val expected = TACProgramBuilder {
            x assign LNot(yS)
            z assign yS
        }
        runAndCompare(expected, prog)
    }


    @Test
    fun normalize2() {
        val prog = TACProgramBuilder {
            y assign LNot(xS)
            z assign y
            u assign LNot(zS)
        }
        val expected = TACProgramBuilder {
            y assign LNot(xS)
            z assign y
            u assign x
        }
        runAndCompare(expected, prog)
    }


    @Test
    fun normalize3() {
        val prog = TACProgramBuilder {
            u assign LNot(xS)
            v assign LNot(yS)
            w assign LAnd(uS, vS)
            assumeNot(w)
        }
        val res = NegationNormalizer(prog.code).rewrite()
        CmdsFolder.fold(res, wS, prog.block(0))
        val last = res.code[prog.block(0)]!!.last() as? TACCmd.Simple.AssumeCmd
        assertNotNull(last, "")
        assertEquals(
            type(txf { LOr(xS, yS) }),
            CmdsFolder.fold(res, last.condExpr, prog.block(0))
        )
    }


    @Test
    fun normalizeNegNegNegNeg() {
        val prog = TACProgramBuilder {
            y assign LNot(xS)
            z assign LNot(yS)
            u assign LNot(zS)
            v assign LNot(uS)
            a assign Ite(vS, Zero, One)
            w assign LNot(vS)
            b assign Ite(wS, Zero, One)
            jumpCond(v)
            jump(1) { nop }
            jump(2) { nop }
        }
        val expected = TACProgramBuilder {
            y assign LNot(xS)
            z assign x
            u assign y
            v assign x
            a assign Ite(xS, Zero, One)
            w assign y
            b assign Ite(xS, One, Zero)
            jumpCond(x)
            jump(1) { nop }
            jump(2) { nop }
        }
        runAndCompare(expected, prog)
    }
}
