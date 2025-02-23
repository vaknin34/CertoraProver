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

package rules.genericrulecheckers.helpers

import analysis.CmdPointer
import analysis.TACTypeChecker
import org.junit.jupiter.api.Test

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.assertThrows
import rules.genericrulecheckers.helpers.InstrumentationPlaceholderCommandsManager.Companion.createPlaceholders
import tac.Tag
import testing.ttl.TACMockLanguage
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACSymbol

class InstrumentationPlaceholderCommandsManagerTest {
    private val coreTACProgram = let {
        val graph = TACMockLanguage.make {
            L1023 = 0
            L(1024, Tag.Bool) `=` `*`
            `if`(L(1024, Tag.Bool)) {
                L1023 = 3
                // split here
                jump()
                L1021 = 3
                L(1022, Tag.Bool) `=` "!L1023 == L1021"
                assume(L(1022, Tag.Bool))
            } `else` {
                L1023 = 4
            }
        }
        val decls = setOf(
            TACSymbol.Var("L1024", Tag.Bool),
            TACSymbol.Var("L1023", Tag.Bit256),
            TACSymbol.Var("L1022", Tag.Bool),
            TACSymbol.Var("L1021", Tag.Bit256),
        )
        CoreTACProgram.empty("")
            .copy(code = graph.code, blockgraph = graph.blockSucc, symbolTable = graph.symbolTable.mergeDecls(decls))
            .let { TACTypeChecker.checkProgram(it) }
    }

    private val graph = coreTACProgram.analysisCache.graph
    private val root = graph.roots.first().ptr
    private val sink1 = graph.sinks.first().ptr
    private val sink2 = let {
        val temp = graph.sinks.last().ptr
        assertTrue(sink1 != temp)
        temp
    }
    private val midPtr = let {
        val cmdCount = graph.code[sink1.block]!!.size
        check(cmdCount > 2)
        CmdPointer(sink1.block, cmdCount / 2)
    }

    @Test
    fun popAllEqualsRepeatPopSingle() {
        val (_, phs1) = createPlaceholders(
            coreTACProgram, listOf(
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.After(root, 4u)
            )
        )
        val (_, phs2) = createPlaceholders(
            coreTACProgram, listOf(
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.After(root, 4u)
            )
        )
        val (_, phs3) = createPlaceholders(
            coreTACProgram, listOf(
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.After(root, 4u)
            )
        )
        val all = phs1.popAll(root)
        assertEquals(all, (0..3).map { phs2.popFirst(root) })
        assertEquals(all, (0..3).map { phs3.popLast(root) }.reversed())
    }

    @Test
    fun popWithoutPlaceholderIsNull() {
        val (_, phs1) = createPlaceholders(
            coreTACProgram, listOf(
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.Replace(midPtr, 4u),
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.Before(sink2, 4u)
            )
        )
        // Using old graph as I am trying an "old" pointer, but it is also a legal pointer in the new graph
        val nexts = graph.succ(midPtr)
        assertEquals(nexts.size, 1)
        assertNull(phs1.popAll(nexts.first()))
        val pred = graph.pred(sink2)
        assertEquals(pred.size, 1)
        assertNull(phs1.popAll(pred.first()))
    }

    @Test
    fun popAfterUsedAllIsNull() {
        val (_, phs1) = createPlaceholders(
            coreTACProgram, listOf(
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.After(root, 4u),
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.After(sink2, 4u),
            )
        )
        for (i in 0..3) {
            assertNotNull(phs1.popFirst(root))
        }
        assertNotNull(phs1.popAll(sink2))
        assertNull(phs1.popFirst(root))
        assertNull(phs1.popAll(sink2))
    }

    @Test
    fun cantPlaceholdSamePtrTwice() {
        assertThrows<IllegalArgumentException> {
            createPlaceholders(
                coreTACProgram, listOf(
                    InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.After(root, 4u),
                    InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.After(root, 4u),
                )
            )
        }
    }

    @Test
    fun placeholdersInDifferentLocations() {
        val (newProg, phs) = createPlaceholders(
            coreTACProgram, listOf(
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.Replace(root, 1u),
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.Replace(midPtr, 2u),
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.Replace(sink1, 3u),
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.Replace(sink2, 4u),
            )
        )
        val newGraph = newProg.analysisCache.graph

        fun checkPtrs(ptr: CmdPointer, amount: Int) {
            assertEquals(phs.sizeAt(ptr), amount.toUInt())
            val ptrs = phs.popAll(ptr)
            assertNotNull(ptrs)
            assertEquals(amount, ptrs!!.size)
            assert(ptrs.all { newGraph.elab(it).cmd is TACCmd.Simple.AnnotationCmd })
        }

        checkPtrs(root, 1)
        checkPtrs(midPtr, 2)
        checkPtrs(sink1, 3)
        checkPtrs(sink2, 4)
    }

    @Test
    fun twoPointersInSameBlock() {
        val midPtr2 = graph.succ(midPtr).first()
        val (newProg, phs) = createPlaceholders(
            coreTACProgram, listOf(
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.Replace(midPtr, 5u),
                InstrumentationPlaceholderCommandsManager.PlaceholdersLocation.Replace(midPtr2, 4u),
            )
        )
        val newGraph = newProg.analysisCache.graph

        fun checkPtrs(ptr: CmdPointer, amount: Int) {
            assertEquals(phs.sizeAt(ptr), amount.toUInt())
            val ptrs = phs.popAll(ptr)
            assertNotNull(ptrs)
            assertEquals(amount, ptrs!!.size)
            assert(ptrs.all { newGraph.elab(it).cmd is TACCmd.Simple.AnnotationCmd })
        }

        checkPtrs(midPtr, 5)
        checkPtrs(midPtr2, 4)
    }
}
