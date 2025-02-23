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

import analysis.enarrow
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import vc.data.TACBuilderAuxiliaries
import vc.data.TACExpr
import vc.data.TACProgramBuilder
import verifier.PolarityCalculator.Polarity

class PolarityCalculatorTest : TACBuilderAuxiliaries() {

    @Test
    fun testAssumeExp() {
        val prog = TACProgramBuilder {
            label("pos")
            u assign v
            assumeExp(uS)

            label("neg")
            x assign y
            assumeExp(LNot(xS))

            label("both")
            a assign c
            assumeExp(Eq(aS, bS))
        }
        val pc = PolarityCalculator(prog.code)
        fun polarity(label : String) =
            pc.polarityOfLhs(
                prog.lcmd(label).enarrow<TACExpr>()
            )
        assertEquals(Polarity.POS, polarity("pos"))
        assertEquals(Polarity.NEG, polarity("neg"))
        assertEquals(Polarity.BOTH, polarity("both"))
    }

}
