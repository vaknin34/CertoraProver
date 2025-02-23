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

class IncrementalMustEqualsTest : MockStackVarMixin, CommandFinderMixin {
    @Test
    fun testBasicEquivalence() {
        val graph = TACMockLanguage.make {
            L1024 = 4
            L1022 = L1024
            L1021 = L1024
            tagNext("site")
            L1021 = "L1021 + 0x3"
        }
        val me = OnDemandMustEqualsAnalysis(graph)
        val site = graph.findCommandOrFail("site")
        Assertions.assertEquals(setOf(L1021, L1024, L1022), me.equivBefore(site, L1021))

        Assertions.assertEquals(setOf(L1021), me.equivAfter(site, L1021))
    }

    @Test
    fun testConditionalJoins() {
        val graph = TACMockLanguage.make {
            `if`(1024, `*`) {
                L1023 = 3
            } `else` {
                L1022 = 2
            }
            `if`(1024, `*`) {
                L1023 = L1022
                L1021 = L1023
            } `else` {
                L1021 = L1023
            }
            tagNext("assign")
            L1020 = L1021
        }
        val me = OnDemandMustEqualsAnalysis(graph)
        val where = graph.findCommandOrFail("assign")
        Assertions.assertEquals(setOf(L1020, L1021, L1023), me.equivAfter(where, L1020))
    }

    @Test
    fun testIndirectAlias() {
        val graph = TACMockLanguage.make {
            L1023 = `*`
            L1021 = L1023
            L1022 = L1023
            L1023 = 4
            tagNext("assign")
            L1024 = L1022
        }
        val me = OnDemandMustEqualsAnalysis(graph)
        val where = graph.findCommandOrFail("assign")
        Assertions.assertEquals(setOf(L1021, L1022, L1024), me.equivAfter(where, L1024))
    }

    @Test
    fun testNoFirstDefAlias() {
        val graph = TACMockLanguage.make {
            L1020 = `*`
            // L1023 is never assigned
            L1021 = L1023
            L1022 = L1023
            L1023 = 4
            tagNext("assign")
            L1024 = L1022
        }
        val me = OnDemandMustEqualsAnalysis(graph)
        val where = graph.findCommandOrFail("assign")
        Assertions.assertEquals(setOf(L1021, L1022, L1024), me.equivAfter(where, L1024))
    }

    @Test
    fun testLoops() {
        val graph = TACMockLanguage.make {
            L1020 = `*`
            `while`(L(1022), "L1020 > 0x0") {
                L1022 = L1021
                L1023 = L1022
            }
            tagNext("assign")
            L1024 = L1023
        }
        val me = OnDemandMustEqualsAnalysis(graph)
        val where = graph.findCommandOrFail("assign")
        Assertions.assertEquals(setOf(L1023, L1024), me.equivAfter(where, L1024))
    }
}