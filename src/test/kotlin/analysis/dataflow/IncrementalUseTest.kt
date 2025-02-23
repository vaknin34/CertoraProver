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

class IncrementalUseTest : MockStackVarMixin, CommandFinderMixin {
    @Test
    fun testBasicUse() {
        val graph = TACMockLanguage.make {
            tagNext("def")
            L1023 = 4
            tagNext("defAndUse")
            L1023 = "L1023 + 0x1"
            tagNext("nextUse")
            L1022 = L1023
        }
        val defSite = graph.findCommandOrFail("def")
        val ua = OnDemandUseAnalysis(graph)
        val useSites = ua.useSitesAfter(L1023, defSite)
        Assertions.assertEquals(1, useSites.size)
        Assertions.assertEquals(setOf("defAndUse"), useSites.toTags(graph))

        val secondDefSite = graph.findCommandOrFail("defAndUse")
        val secondUseSites = ua.useSitesAfter(L1023, secondDefSite)
        Assertions.assertEquals(1, secondUseSites.size)
        Assertions.assertEquals(setOf("nextUse"), secondUseSites.toTags(graph))
    }

    @Test
    fun testConditionalRedefinition() {
        val graph = TACMockLanguage.make {
            tagNext("firstDef")
            L1024 = 4
            tagNext("firstUse")
            L1023 = "L1024 + 0x3"
            `if`(1023, `*`) {
                tagNext("secondDef")
                L1024 = 3
            } `else` {
                L1021 = 1
            }
            tagNext("secondUse")
            L1023 = "L1024 - 0x1"
            exit()
        }
        val firstDef = graph.findCommandOrFail("firstDef")
        val ua = OnDemandUseAnalysis(graph)
        val uses = ua.useSitesAfter(L1024, firstDef)
        Assertions.assertEquals(2, uses.size)
        Assertions.assertEquals(setOf("firstUse", "secondUse"), uses.toTags(graph))

        val secondDef = graph.findCommandOrFail("secondDef")
        val secondUses = ua.useSitesAfter(L1024, secondDef)
        Assertions.assertEquals(1, secondUses.size)
        Assertions.assertEquals(setOf("secondUse"), secondUses.toTags(graph))
    }

    @Test
    fun testUseInLoop() {
        val graph = TACMockLanguage.make {
            tagNext("firstDef")
            L1024 = 4
            tagNext("soleUse")
            L1023 = "L1024 * 0x2"
            `while`(L(1022), "L1023 == 0x0") {
                tagNext("firstUse")
                L1023 = "L1024 - 0x1"
                tagNext("secondDefAndUse")
                L1024 = "L1024 - 0x1"
            }
            tagNext("finalUse")
            L1023 = "L1024 + 0x10"
        }
        val ua = OnDemandUseAnalysis(graph)
        val firstDef = graph.findCommandOrFail("firstDef")
        val secondDef = graph.findCommandOrFail("secondDefAndUse")

        val useSitesOfFirst = ua.useSitesAfter(L1024, firstDef)
        Assertions.assertEquals(4, useSitesOfFirst.size)
        Assertions.assertEquals(setOf("soleUse", "firstUse", "secondDefAndUse", "finalUse"), useSitesOfFirst.toTags(graph))

        val useSitesOfSecond = ua.useSitesAfter(L1024, secondDef)
        Assertions.assertEquals(3, useSitesOfSecond.size)
        Assertions.assertEquals(setOf("firstUse", "secondDefAndUse", "finalUse"), useSitesOfSecond.toTags(graph))
    }
}