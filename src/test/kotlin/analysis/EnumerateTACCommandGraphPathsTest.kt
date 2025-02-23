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

package analysis

import com.certora.collect.*
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertDoesNotThrow
import tac.StartBlock
import vc.data.*

internal class EnumerateTACCommandGraphPathsTest {
    @Test
    fun testTacCommandGraphCreation01() {
        val dummyCmd = TACCmd.Simple.AssumeCmd(TACSymbol.True)
        val n1 = StartBlock.copy(origStartPc = 0)
        val n2 = StartBlock.copy(origStartPc = 1)
        val n3 = StartBlock.copy(origStartPc = 2)
        val blockGraph = BlockGraph(
            n1 to treapSetOf(n2),
            n2 to treapSetOf(n3)
        )
        val code = mapOf(
            n1 to listOf(dummyCmd),
            n2 to listOf(dummyCmd),
            n3 to listOf(dummyCmd)
        )

        assertDoesNotThrow {
            TACCommandGraph(blockGraph, code, TACSymbolTable.empty(), name = "")
        }

        assertTrue(true)
    }

}
