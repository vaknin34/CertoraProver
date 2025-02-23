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

package parser

import allocator.Allocator
import org.junit.jupiter.api.Test
import tac.NBId
import tac.BlockIdentifier

class TestTacSerde {
    private val blocks = listOf(
        BlockIdentifier(0, 2, 5, 666, 0, 555),
        BlockIdentifier(10_000_000, 2_000_000, 5_000_000, 666_000_000, 0, 555_000),
        BlockIdentifier(
            Int.MAX_VALUE,
            Int.MAX_VALUE,
            Int.MAX_VALUE,
            Int.MAX_VALUE,
            Int.MAX_VALUE,
            Int.MAX_VALUE,
        ),
        BlockIdentifier(
            Int.MIN_VALUE,
            Int.MIN_VALUE,
            Int.MIN_VALUE,
            Int.MIN_VALUE,
            Int.MIN_VALUE,
            Int.MIN_VALUE,
        ),
    )
    val checkSerde = { block: NBId ->
        val backToLife = NBId.parseString(block.toString())
        assert(block is BlockIdentifier == backToLife is BlockIdentifier)
        assert(block.compareTo(backToLife) == 0)
    }

    @Test
    fun tacSerde() {
        for (block in blocks) {
            checkSerde(block)
            val canon = block.toCanon { _, it -> it }
            checkSerde(canon)
            assert(block.compareTo(canon) == 1)
            assert(canon.compareTo(block) == -1)
            assert(block.getCallId() == canon.getCallId())

            val canon6 = block.toCanon { id, _ -> id.ordinal }
            if (block.fromDecompiler()) {
                assert(block.origStartPc == canon6.origStartPc)
            } else {
                assert(canon6.origStartPc == Allocator.Id.PC_FOR_NBID.ordinal)
            }
            assert(canon6.freshCopy == Allocator.Id.BLOCK_FRESH_COPY.ordinal)
        }
    }

    @Test
    fun legacy() {
        for (block in blocks) {
            for (trailing in listOf(0, 2, 5, 666, 0, 555, 777)) {
                checkSerde(NBId.parseString("${block}_0_$trailing"))
                checkSerde(NBId.parseString("${trailing}_0_$block"))
                assert(kotlin.runCatching { NBId.parseString("${block}_0_0_$trailing") }.isFailure)
            }
        }
    }
}
