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

import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import tac.StartBlock

internal class ExpPointerTest {

    @Test
    fun isPrefixOf() {
        val nonStartBlock = StartBlock.copy(origStartPc = 1)

        val startBlock0 = CmdPointer(StartBlock, 0)
        val startBlock3 = CmdPointer(StartBlock, 3)
        val nonStartBlock0 = CmdPointer(nonStartBlock, 0)

        assertTrue(ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3)) isPrefixOf
                ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3, 4)))
        assertFalse(ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3)) isPrefixOf
                ExpPointer(startBlock3, ExpPointer.Path(1, 2, 3, 4)))
        assertFalse(ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3)) isPrefixOf
                ExpPointer(nonStartBlock0, ExpPointer.Path(1, 2, 3, 4)))


        assertTrue(ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3, 4)) isPrefixOf
                ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3, 4)))
        assertFalse(ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3, 4)) isPrefixOf
                ExpPointer(startBlock3, ExpPointer.Path(1, 2, 3, 4)))
        assertFalse(ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3, 4)) isPrefixOf
                ExpPointer(nonStartBlock0, ExpPointer.Path(1, 2, 3, 4)))

        assertFalse(ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3, 4)) isPrefixOf
                ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3)))


        assertFalse(ExpPointer(startBlock0, ExpPointer.Path(1, 1, 3)) isPrefixOf
                ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3)))
        assertFalse(ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3)) isPrefixOf
                ExpPointer(startBlock0, ExpPointer.Path(1, 1, 3)))
        assertFalse(ExpPointer(startBlock0, ExpPointer.Path(1, 2, 3)) isPrefixOf
                ExpPointer(startBlock0, ExpPointer.Path(1, 1, 3, 5)))
    }
}
