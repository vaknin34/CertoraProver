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

import analysis.CommandWithRequiredDecls
import analysis.icfg.Summarizer.toCode
import analysis.opt.intervals.IntervalsRewriter
import normalizer.MemoryOverlapFixer
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import tac.Tag
import vc.data.*
import java.math.BigInteger

class MemoryOverlapTest {

    private fun testEarlyUpdates(readLoc: Int, readValue: BigInteger, writeLoc: Int, writeValue: BigInteger, expected: BigInteger) {
        val (cmds, ret) = MemoryOverlapFixer.WriteToUpdate.updateFromEarlierWrite(
            readLoc.toBigInteger(), readValue.asTACSymbol(), writeLoc.toBigInteger(), writeValue.asTACSymbol()
        )
        testUpdates(cmds, ret, expected)
    }

    private fun testLaterUpdates(readLoc: Int, readValue: BigInteger, writeLoc: Int, writeValue: BigInteger, expected: BigInteger) {
        val (cmds, ret) = MemoryOverlapFixer.WriteToUpdate.updateFromLaterWrite(
            readLoc.toBigInteger(), readValue.asTACSymbol(), writeLoc.toBigInteger(), writeValue.asTACSymbol()
        )
        testUpdates(cmds, ret, expected)
    }

    private fun testUpdates(cmds: CommandWithRequiredDecls<TACCmd.Simple>, ret: TACSymbol.Var, expected: BigInteger) {
        val tmp = TACKeyword.TMP(Tag.Bool).toUnique()
        val cmdsWithAssert = CommandWithRequiredDecls(cmds.cmds + listOf(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(tmp, TACExpr.BinRel.Eq(ret.asSym(), expected.asTACExpr)),
            TACCmd.Simple.AssertCmd(tmp, "false instrumentation or expected value")
        ), cmds.varDecls + tmp)
        val simplified = IntervalsRewriter.rewrite(cmdsWithAssert.toCode(0), repeat = 1, handleLeinoVars = false)
        val g = simplified.analysisCache.graph
        Assertions.assertNotNull(g.commands.singleOrNull())
        Assertions.assertEquals(TACCmd.Simple.NopCmd, g.commands.first().cmd)
    }

    @Test
    fun testEarlyWrite() {
        testEarlyUpdates(1,
            "2222222222222222222222222222222222222222222222222222222222222222".toBigInteger(16),
            0,
            "1111111111111111111111111111111111111111111111111111111111111111".toBigInteger(16),
            "1111111111111111111111111111111111111111111111111111111111111122".toBigInteger(16)
        )
        testEarlyUpdates(3,
            "2222222222222222222222222222222222222222222222222222222222222222".toBigInteger(16),
            2,
            "1111111111111111111111111111111111111111111111111111111111111111".toBigInteger(16),
            "1111111111111111111111111111111111111111111111111111111111111122".toBigInteger(16)
        )
        testEarlyUpdates(4,
            "2222222222222222222222222222222222222222222222222222222222222222".toBigInteger(16),
            2,
            "1111111111111111111111111111111111111111111111111111111111111111".toBigInteger(16),
            "1111111111111111111111111111111111111111111111111111111111112222".toBigInteger(16)
        )
        testEarlyUpdates(32,
            "2222222222222222222222222222222222222222222222222222222222222222".toBigInteger(16),
            16,
            "1111111111111111111111111111111111111111111111111111111111111111".toBigInteger(16),
            "1111111111111111111111111111111122222222222222222222222222222222".toBigInteger(16)
        )
        testEarlyUpdates(64,
            "2222222222222222222222222222222222222222222222222222222222222222".toBigInteger(16),
            33,
            "1111111111111111111111111111111111111111111111111111111111111111".toBigInteger(16),
            "1122222222222222222222222222222222222222222222222222222222222222".toBigInteger(16)
        )
    }

    @Test
    fun testLaterWrite() {
        testLaterUpdates(1,
            "2222222222222222222222222222222222222222222222222222222222222222".toBigInteger(16),
            2,
            "1111111111111111111111111111111111111111111111111111111111111111".toBigInteger(16),
            "2211111111111111111111111111111111111111111111111111111111111111".toBigInteger(16)
        )
        testLaterUpdates(1,
            "2222222222222222222222222222222222222222222222222222222222222222".toBigInteger(16),
            3,
            "1111111111111111111111111111111111111111111111111111111111111111".toBigInteger(16),
            "2222111111111111111111111111111111111111111111111111111111111111".toBigInteger(16)
        )
        testLaterUpdates(16,
            "2222222222222222222222222222222222222222222222222222222222222222".toBigInteger(16),
            32,
            "1111111111111111111111111111111111111111111111111111111111111111".toBigInteger(16),
            "2222222222222222222222222222222211111111111111111111111111111111".toBigInteger(16)
        )
        testLaterUpdates(33,
            "2222222222222222222222222222222222222222222222222222222222222222".toBigInteger(16),
            64,
            "1111111111111111111111111111111111111111111111111111111111111111".toBigInteger(16),
            "2222222222222222222222222222222222222222222222222222222222222211".toBigInteger(16)
        )
    }
}
