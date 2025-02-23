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

package vc.data

import com.certora.collect.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows
import tac.CallId
import tac.NBId
import tac.StartBlock

class TACProgramTests {

    @Test
    fun testDefineEntryBlock() {
        val blocks: List<NBId> = List(6) { createBlock(it) }

        val blockGraph: BlockGraph = BlockGraph(
            blocks[1] to blocks.subList(2, 4).toTreapSet(),
            blocks[2] to blocks.subList(3, 5).toTreapSet(),
            blocks[3] to treapSetOf(blocks[5]),
            blocks[4] to treapSetOf(blocks[5])
        )
        val name = "well-formed graph"

        val program = CoreTACProgram(
            mapOf(),
            blockGraph,
            name,
            TACSymbolTable.empty(),
            UfAxioms.empty(),
            IProcedural.empty(),
            false
        )

        assertEquals(blocks[1], program.entryBlockId)
    }

    @Test
    fun testEntryBlockWithEmptyGraph() {
        val blockGraph: BlockGraph = BlockGraph()

        val name = "Empty Program"
        assertThrows<IllegalStateException> {
            CoreTACProgram(
                mapOf(),
                blockGraph,
                name,
                TACSymbolTable.empty(),
                UfAxioms.empty(),
                IProcedural.empty(),
                false
            ).entryBlockId
        }
    }

    @Test
    fun failureOnAmbiguousEntry() {
        val blocks: List<NBId> = List(6) { createBlock(it) }

        val blockGraph: BlockGraph = BlockGraph(
            blocks[0] to treapSetOf(blocks[2]),
            blocks[1] to blocks.subList(2, 4).toTreapSet(),
            blocks[2] to blocks.subList(3, 5).toTreapSet(),
            blocks[3] to treapSetOf(blocks[5]),
        )

        val name = "ambiguous graph"

        assertThrows<IllegalStateException> {
            CoreTACProgram(
                mapOf(),
                blockGraph,
                name,
                TACSymbolTable.empty(),
                UfAxioms.empty(),
                IProcedural.empty(),
                false
            ).entryBlockId
        }

    }

    private fun createBlock(id: CallId): NBId = StartBlock.copy(calleeIdx = id)
}
