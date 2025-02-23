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
import vc.data.TACSymbol

class LiveVariableAnalysisTest : MockStackVarMixin, CommandFinderMixin {
    @Test
    fun testBasicLiveness() {
        val graph = TACMockLanguage.make {
            tagNext("pt1")
            L1024 = 4
            tagNext("pt2")
            L1024 = 3
            tagNext("pt3")
            L1023 = "L1024 + L1023"
        }
        val lva = LiveVariableAnalysis(graph)

        val pt1 = graph.findCommandOrFail("pt1")
        Assertions.assertEquals(setOf(L1023), lva.liveVariablesBefore(pt1))
        Assertions.assertEquals(setOf(L1023), lva.liveVariablesAfter(pt1))

        val pt2 = graph.findCommandOrFail("pt2")
        Assertions.assertEquals(setOf(L1023), lva.liveVariablesBefore(pt2))
        Assertions.assertEquals(setOf(L1023, L1024), lva.liveVariablesAfter(pt2))

        val pt3 = graph.findCommandOrFail("pt3")
        Assertions.assertEquals(setOf(L1023, L1024), lva.liveVariablesBefore(pt3))
        Assertions.assertEquals(setOf<TACSymbol.Var>(), lva.liveVariablesAfter(pt3))
    }
}
