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

package report.dumps

import org.junit.jupiter.api.Test

import org.junit.jupiter.api.Assertions.*
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import java.math.BigInteger

class TACStatisticsTest : TACBuilderAuxiliaries() {

    @Test
    fun basicStatsTwoDiamondTAC() {
        val wm = wordMapVar("wm")
        val boo = boolVar("boo")
        val prog = TACProgramBuilder {
            f assign Div(aS, bS)
            boo assign Eq(fS, aS)
            jumpCond(boo)
            jump(1) {
                c assign d
                a assign BWNot(c.asSym())
                a assign BWXOr(a.asSym(), c.asSym())
                jump(3) {
                    // This is actually after first conditional, so it will be the second diamond
                    a assign Mul(aS, dS)
                    g assign Mul(Add(eS, fS), cS)
                    boo assign Lt(aS, gS)
                    jumpCond(boo)
                    jump(4) {
                        c assign Add(aS, gS)
                        wm assign Store(wm.asSym(), eS, v = cS)
                        jump(6) {
                            d assign Select(wm.asSym(), eS)
                            a assign 0
                            y assign Eq(dS, aS)
                            assert(y, "This should be fine")
                        }
                    }
                    jump(5) {
                        a assign Div(Add(cS, gS), Mul(aS, Div(bS, cS)))
                        wm assign Store(wm.asSym(), Add(eS, eS), v = aS)
                        wm assign Store(wm.asSym(), Add(eS, fS), v = Add(Select(wm.asSym(), Add(eS, eS)), eS))
                        a assign Div(Select(wm.asSym(), Add(eS, fS)), fS)
                        wm assign Store(wm.asSym(), eS, v = aS)
                        jump(6)
                    }
                }
            }
            jump(2) {
                a assign 2
                jump(3)
            }
        }

        val stats = TACStatistics.invoke(prog.code)
        assertEquals(stats.blockCount, 7)
        assertEquals(stats.branchCount, 2)
        assertEquals(3, stats.loadCount)
        assertEquals(4, stats.storeCount)
        assertEquals(BigInteger.valueOf(4), stats.pathCount)
        val probablyNonLinearCount =
            stats.probablyNonLinearCounts.map { it.value }.sum()
        assertTrue(probablyNonLinearCount >= 3) {
            "Expected more than 3 non linear expressions, but got " +
                "$probablyNonLinearCount"
        }
        val bitwiseCount = stats.bitwiseCounts.map { it.value }.sum()
        assertTrue(bitwiseCount == 1) {
            "Expected a single bitwise expression, but got $bitwiseCount"
        }
        assertNotEquals(0, stats.totalBlockDifficulty,
            "This should be somewhat difficult")
    }
}
