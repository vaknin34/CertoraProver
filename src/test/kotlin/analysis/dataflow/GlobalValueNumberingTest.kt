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

package analysis.dataflow
import analysis.CommandFinderMixin
import analysis.MockStackVarMixin
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import testing.ttl.TACMockLanguage
import vc.data.TACKeyword
import vc.data.TACSymbol

class GlobalValueNumberingTest : MockStackVarMixin, CommandFinderMixin {

    @Test
    fun testBasicEquivalence() {
        val graph = TACMockLanguage.make {
            L1024 = 4
            L1022 = L1024
            tagNext("equal")
            L1021 = L1024
            tagNext("site")
            L1021 = "L1021 + 0x3"
            tagNext("end")
            L1024 = `*`
        }
        val gvn = GlobalValueNumbering(graph)
        val equal = graph.findCommandOrFail("equal")
        val site = graph.findCommandOrFail("site")
        val end = graph.findCommandOrFail("end")

        Assertions.assertEquals(setOf(L1021, L1022, L1024), gvn.findCopiesAt(site, (equal to L1022)))
        Assertions.assertEquals(setOf(L1022, L1024), gvn.findCopiesAt(end, (equal to L1022)))
    }

    @Test
    fun loopUpdatesAndJoins() {
        val graph = TACMockLanguage.make {
            freePointer `=` `*`
            `while`(L(1020), "L1025 < 0x4") {
                tagNext("loopStart")
                L1023 = 0
                `if`(1021, `*`) {
                    tagNext("read")
                    L1022 = freePointer
                    freePointer `=` `*`
                } `else` {
                    L1024 = 1
                }
             }
        }
        val gvn = GlobalValueNumbering(graph)
        val start = graph.findCommandOrFail("loopStart")
        val read = graph.findCommandOrFail("read")
        Assertions.assertEquals(
            setOf(TACKeyword.MEM64.toVar()),
            gvn.findCopiesAt(read, start to TACKeyword.MEM64.toVar())
        )
    }

    @Test
    fun testSimpleJoin() {
        val graph = TACMockLanguage.make {
            L1020 = 3
            tagNext("there")
            `if`(1021, `*`) {
                L1021 = L1020
            } `else` {
                L1021 = L1020
            }
            tagNext("here")
            L1022 = L1021 // Make sure the L1020 class is live here
        }
        val here = graph.findCommandOrFail("here")
        val there = graph.findCommandOrFail("there")
        val gvn = GlobalValueNumbering(graph)
        Assertions.assertEquals(setOf(L1021, L1020), gvn.findCopiesAt(here, (there to L1020)))
    }
    @Test
    fun testLiveDead() {
        val graph = TACMockLanguage.make {
            L1020 = `*`
            tagNext("start")
            L1021 = L1020
            `if`(1022, `*`) {
                L1023 = `*`
            } `else` {
                L1023 = `*`
            }
            L1023 = L1021
            tagNext("end")
            L1024 = L1023
        }
        val gvn = GlobalValueNumbering(graph)
        val start = graph.findCommandOrFail("start")
        val end = graph.findCommandOrFail("end")
        Assertions.assertEquals(setOf(L1020, L1021, L1023), gvn.findCopiesAt(end, start to L1020))
    }

    @Test
    fun testJoins() {
        val graph = TACMockLanguage.make {
            L1020 = 3
            `if` (1024, `*`) {
                L1020 = 4
            } `else` {
                L1020 = 5
            }
            tagNext("join")
            L1021 = L1020
            `if` (1024, `*`) {
                L1020 = "L1020 + 0x03"
            } `else` {
                L1020 = "L1020 + 0x01"
            }
            L1022 = L1021
            tagNext("here")
            L1024 = L1022
            tagNext("there")
            L1024 = L1020
        }
        val join = graph.findCommandOrFail("join")
        val here = graph.findCommandOrFail("here")
        val there = graph.findCommandOrFail("there")
        val gvn = GlobalValueNumbering(graph)
        Assertions.assertEquals(setOf(L1021, L1022), gvn.findCopiesAt(here, (join to L1020)))
        Assertions.assertEquals(setOf(L1021, L1022, L1024), gvn.findCopiesAt(there, (join to L1020)))
    }
    @Test
    fun testIndirectAlias() {
        val graph = TACMockLanguage.make {
            L1023 = `*`
            L1021 = L1023
            L1022 = L1023
            L1023 = 4
            L1024 = L1022
            tagNext("assign")
            L1020 = `*`
        }
        val gvn = GlobalValueNumbering(graph)
        val where = graph.findCommandOrFail("assign")
        Assertions.assertEquals(setOf(L1021, L1022, L1024), gvn.findCopiesAt(where, (where to L1024)))
    }

    @Test
    fun testNoFirstDefAlias() {
        val graph = TACMockLanguage.make {
            L1020 = `*`
            // L1023 is never assigned
            L1021 = L1023
            L1022 = L1023
            L1023 = 4
            L1024 = L1022
            tagNext("assign")
            L1020 = `*`
        }
        val gvn = GlobalValueNumbering(graph)
        val where = graph.findCommandOrFail("assign")
        Assertions.assertEquals(setOf(L1021, L1022, L1024), gvn.findCopiesAt(where, (where to L1024)))
    }
    @Test
    fun testLoopFragment() {
        val graph = TACMockLanguage.make {
            L1020 = `*`
            L1022 = "L1021 + 0x1"
            `if`(1020, `*`) {
                tagNext("init")
                L1021 = 1
            }`else`{
                tagNext("update")
                L1021 = "L1021 + 0x1"
            }
            tagNext("exit")
            L1023 = L1021 // Make sure the L1021 class is live here
        }

        val gvn = GlobalValueNumbering(graph)
        val end = graph.findCommandOrFail("exit")
        Assertions.assertEquals(setOf<TACSymbol.Var>(L1021), gvn.findCopiesAt(end, (end to L1021)))
    }
    @Test
    fun testWhile() {
        val graph = TACMockLanguage.make {
            L1023 = 1
            L1024 = 1
            L1022 = 0
            `while`(L(100), "L1021 < 0x3") {
                L1022 = "L1023 + L1024"
                L1024 = "L1024 + 0x1"
            }
            tagNext("join")
            L1023 = L1024
            L1024 = `*`
            L1021 = L1023
            tagNext("end")
            L1020 = `*`
        }
        val gvn = GlobalValueNumbering(graph)
        val join = graph.findCommandOrFail("join")
        val end = graph.findCommandOrFail("end")
        Assertions.assertEquals(setOf(L1023, L1021), gvn.findCopiesAt(end, (join to L1024)))
    }
}
