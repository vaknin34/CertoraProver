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

import analysis.CmdPointer
import com.certora.collect.*
import datastructures.stdcollections.*
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.assertThrows
import tac.NBId
import tac.CallId
import tac.emptyTags
import tac.StartBlock
import tac.Tag
import tac.Tags

class PatchingTACProgramTests {

    @Test
    fun testAddingOpenBlock() {
        val blocks: List<NBId> = List(6) { createBlock(it) }

        val blockGraph: BlockGraph = BlockGraph(
            blocks[0] to treapSetOf(blocks[1]),
            blocks[1] to blocks.subList(2, 4).toTreapSet(),
            blocks[2] to blocks.subList(3, 5).toTreapSet(),
            blocks[3] to treapSetOf(blocks[5]),
            blocks[4] to treapSetOf(blocks[5]),
            blocks[5] to treapSetOf(),

            )

        val symbol = TACKeyword.TMP(Tag.Bool, "dummyVar").toUnique("!")
        val tags = Tags(treapSetOf(symbol))

        val symbolTable = TACSymbolTable(treapSetOf(), treapSetOf(), tags, mapOf())

        val code: BlockNodes<TACCmd.Simple> = blocks.associateWith {
            if (blockGraph[it]!!.size > 1) {
                val dest = blockGraph[it]!!.elementAt(0)
                val elseDest = blockGraph[it]!!.elementAt(1)
                listOf(TACCmd.Simple.JumpiCmd(dest, elseDest, symbol))
            } else {
                listOf(TACCmd.Simple.NopCmd)
            }
        }


        val name = "well-formed graph"

        val program = CoreTACProgram(
            code,
            blockGraph,
            name,
            symbolTable,
            UfAxioms.empty(),
            IProcedural.empty(),
        )


        val p = program.toPatchingProgram()

        val block1 = blocks[1]
        val block3 = blocks[3]
        val block4 = blocks[4]

        assertEquals(treapSetOf(blocks[2], block3), p.getSuccessors(block1))


        val openBlock = p.createOpenBlockFrom(block1)

        p.replaceCommand(CmdPointer(block1, 0), listOf(TACCmd.Simple.JumpiCmd(openBlock, block3, symbol)))
        p.populateBlock(openBlock, listOf(TACCmd.Simple.JumpCmd(block4)))
        val updatedProgram = p.toCode()


        assertEquals(treapSetOf(block4), updatedProgram.second[openBlock])
        assertEquals(treapSetOf(openBlock, block3), updatedProgram.second[block1])
    }

    @Test
    fun testInvalidOpenBlock() {
        val blocks: List<NBId> = List(2) { createBlock(it) }

        val block0 = blocks[0]
        val block1 = blocks[1]



        val blockGraph: BlockGraph = BlockGraph(
                block0 to treapSetOf(block1),
                block1 to treapSetOf()
        )


        val code: BlockNodes<TACCmd.Simple> = mapOf(
                block0 to listOf(TACCmd.Simple.JumpCmd(block1)),
                block1 to listOf(TACCmd.Simple.NopCmd)
        )


        val symbolTable = TACSymbolTable(treapSetOf(), treapSetOf(), emptyTags(), mapOf())
        val program = CoreTACProgram(
                code,
                blockGraph,
                "malformed block",
                symbolTable,
                UfAxioms.empty(),
                IProcedural.empty(),
        )

        val p = program.toPatchingProgram()

        val openBlock = p.createOpenBlockFrom(block0)
        p.replaceCommand(CmdPointer(block0, 0), listOf(TACCmd.Simple.JumpCmd(openBlock)))

        val thrown = assertThrows<IllegalArgumentException> { p.populateBlock(openBlock, listOf(TACCmd.Simple.NopCmd)) }
        assertEquals(thrown.message, "No successors (inferred or explicit) for open block $openBlock")

        assertThrows<IllegalStateException> { p.toCode() }.also { assertEquals("cannot finalize program patch if there are open blocks: [$openBlock]", it.message) }
    }


    private fun createBlock(id: CallId): NBId = StartBlock.copy(calleeIdx = id)
}
