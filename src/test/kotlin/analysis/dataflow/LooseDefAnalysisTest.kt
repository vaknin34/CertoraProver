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
import analysis.TACCommandGraph
import analysis.TACMockUtils
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import testing.ttl.TACMockLanguage
import vc.data.TACSymbol
import tac.Tag
import java.util.stream.Stream

class LooseDefAnalysisTest : CommandFinderMixin, MockStackVarMixin {
    @Test
    fun testIncrementalDef() {
        val graph = TACMockLanguage.make {
            // should not be tracked
            L1023 = 6
            L1024 = `*`
            `if`(L(1024)) {
                tagNext("def1")
                L1023 = 4
            } `else` {
                tagNext("def2")
                L1023 = 3
            }
            tagNext("write")
            L1020 = "L1023 + 0x3"
            exit()
        }
        val du = LooseDefAnalysis(graph)
        val final = TACMockUtils.commandWithTagOrFail(graph, "write")
        val res = du.defSitesOf(TACSymbol.Var("L1023", Tag.Bit256), final)
        Assertions.assertEquals(2, res.size)
        val tags = res.toTags(graph)
        Assertions.assertEquals(2, tags.size)
        Assertions.assertEquals(setOf("def1", "def2"), tags)
    }

    @Test
    fun testDefsOfDef() {
        val graph = TACMockLanguage.make {
            tagNext("first")
            L1023 = 3
            tagNext("second")
            L1023 = 4
        }
        val du = LooseDefAnalysis(graph)
        val final = graph.findCommandOrFail("second")
        val defSites = du.defSitesOf(L1023, final)
        Assertions.assertEquals(1, defSites.size)
        Assertions.assertEquals(setOf("first"), defSites.toTags(graph))
    }

    @Test
    fun testDefWithinLoop() {
        val graph = TACMockLanguage.make {
            tagNext("firstDef")
            L1024 = 4
            `while`(L(1022), "L1024 == 0x0") {
                tagNext("use")
                L1023 = "L1023 + L1024"
                tagNext("nextDef")
                L1024 = "L1023 - L1024"
            }
        }
        val du = LooseDefAnalysis(graph)
        val use = graph.findCommandOrFail("use")
        val defSites = du.defSitesOf(L1024, use)
        Assertions.assertEquals(2, defSites.size)
        Assertions.assertEquals(setOf("firstDef", "nextDef"), defSites.toTags(graph))
    }

    @Test
    fun testDefBeforeLoop() {
        val graph = TACMockLanguage.make {
            tagNext("def")
            L1024 = 4
            `while`(L(1022), "L1022 == 0x0") {
                L1022 = "L1022 - 0x1"
            }
            tagNext("firstUse")
            L1022 = L1024
        }
        val du = LooseDefAnalysis(graph)
        val use = graph.findCommandOrFail("firstUse")
        val defSites = du.defSitesOf(L1024, use)
        Assertions.assertEquals(1, defSites.size)
        Assertions.assertEquals(setOf("def"), defSites.toTags(graph))
    }

    @Test
    fun testConditionalDef() {
        val graph = TACMockLanguage.make {
            tagNext("origDef")
            L1024 = 3
            `if`(1023, `*`) {
                tagNext("secondDef")
                L1024 = 4
            } `else` {
                nop
            }
            `if`(1023, `*`) {
                exit()
            } `else` { nop }
            tagNext("use")
            L1023 = "L1024 + 0x3"
            exit()
        }
        val du = LooseDefAnalysis(graph)
        val useSite = graph.findCommandOrFail("use")
        val defSites = du.defSitesOf(L1024, useSite)
        Assertions.assertEquals(2, defSites.size)
        Assertions.assertEquals(setOf("origDef", "secondDef"), defSites.toTags(graph))
    }
}
