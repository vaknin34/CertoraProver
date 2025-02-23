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

import analysis.CmdPointer
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import tac.StartBlock
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder

class HeuristicalDifficultyAnalysisTest : TACBuilderAuxiliaries() {

    val i0 = intVar("i0")
    val i1 = intVar("i1")
    val i2 = intVar("i2")
    val i3 = intVar("i3")
    val i4 = intVar("i4")
    val i5 = intVar("i5")
    val i6 = intVar("i6")
    val i7 = intVar("i7")

    val i0S = i0.asSym()
    val i1S = i1.asSym()
    val i2S = i2.asSym()
    val i3S = i3.asSym()
    val i4S = i4.asSym()
    val i5S = i5.asSym()
    val i6S = i6.asSym()
    val i7S = i7.asSym()

    @Test
    fun t1() {
        val p = TACProgramBuilder {
            i0 assign IntMul(jS, kS)
            i1 assign IntDiv(i0S, i2S)
            i2 assign IntDiv(i0S, number(3)) // division by constant -- should not be counted as it's effectively linear
            assert(true)
        }.code

        val analysis = CountDifficultOps(p)
        val startBlockDiff = analysis[StartBlock]!!
        startBlockDiff.asText
        assertTrue(startBlockDiff.isDifficult())

        assertEquals(1, startBlockDiff.getOccurrenceCount(DifficultOp.Div))
        assertEquals(1, startBlockDiff.getOccurrenceCount(DifficultOp.Mul))
        assertEquals(0, startBlockDiff.getOccurrenceCount(DifficultOp.Ite))
        assertEquals(0, startBlockDiff.getOccurrenceCount(DifficultOp.SDiv))
        assertEquals(
            listOf(
                CmdPointer(StartBlock, 0),
                CmdPointer(StartBlock, 1),
            ),
            startBlockDiff.heuristicallyDifficultCmds.toList()
        )
    }

    @Test
    fun t2() {
        val p = TACProgramBuilder {
            i0 assign IntMul(jS, number(2)) // linear not counted
            i1 assign IntDiv(i0S, i2S)
            i2 assign IntDiv(i0S, number(3)) // division by constant -- should not be counted as it's effectively linear
            i3 assign IntDiv(i1S, i2S)
            assert(true)
        }.code

        val analysis = CountDifficultOps(p)
        val startBlockDiff = analysis[StartBlock]!!
        startBlockDiff.asText
        assertTrue(startBlockDiff.isDifficult())

        assertEquals(2, startBlockDiff.getOccurrenceCount(DifficultOp.Div))
        assertEquals(0, startBlockDiff.getOccurrenceCount(DifficultOp.Mul))
        assertEquals(0, startBlockDiff.getOccurrenceCount(DifficultOp.Ite))
        assertEquals(0, startBlockDiff.getOccurrenceCount(DifficultOp.SDiv))
        assertEquals(
            listOf(
                CmdPointer(StartBlock, 1),
                CmdPointer(StartBlock, 3),
            ),
            startBlockDiff.heuristicallyDifficultCmds.toList()
        )
    }


    @Test
    fun t3() {
        val p = TACProgramBuilder {
            i1 assign Ite(xS, iS, jS)
            i2 assign Ite(xS, iS, jS)
            i3 assign Ite(xS, iS, jS)
            i4 assign Ite(xS, iS, jS)
            i5 assign Ite(xS, iS, jS)
            i6 assign Ite(xS, iS, jS)
            i7 assign Ite(xS, iS, jS)
            i2 assign IntDiv(i0S, number(3)) // division by constant -- should not be counted as it's effectively linear
            i3 assign IntMul(i1S, number(4)) // linear not counted
            assert(true)
        }.code

        val analysis = CountDifficultOps(p)
        val startBlockDiff = analysis[StartBlock]!!
        startBlockDiff.asText
        assertTrue(startBlockDiff.isDifficult())

        assertEquals(0, startBlockDiff.getOccurrenceCount(DifficultOp.Div))
        assertEquals(0, startBlockDiff.getOccurrenceCount(DifficultOp.Mul))
        assertEquals(7, startBlockDiff.getOccurrenceCount(DifficultOp.Ite))
        assertEquals(0, startBlockDiff.getOccurrenceCount(DifficultOp.SDiv))
        assertEquals(
            listOf(
                CmdPointer(StartBlock, 0),
                CmdPointer(StartBlock, 1),
                CmdPointer(StartBlock, 2),
                CmdPointer(StartBlock, 3),
                CmdPointer(StartBlock, 4),
                CmdPointer(StartBlock, 5),
                CmdPointer(StartBlock, 6),
            ),
            startBlockDiff.heuristicallyDifficultCmds.toList()
        )
    }
}

