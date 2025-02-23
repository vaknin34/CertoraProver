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

package algorithms

import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class LongestPathTest {

    @Test
    fun testMaxDistance01() {

        /*
          a single diamond
        0 - 1 \
          \ 2 - 3
         */
        val graph = mapOf(
            0 to setOf(1, 2),
            1 to setOf(3),
            2 to setOf(3),

            )

        val topoOrder = topologicalOrder(graph)

        assertEquals(2, longestPathLength(topoOrder, graph))
    }


    @Test
    fun testMaxDistance02() {

        /*
          a single diamond, with one  longer branch
        0 - 1 ---- \
          \ 2 - 3 - 4
         */
        val graph = mapOf(
            0 to setOf(1, 2),
            2 to setOf(3),
            3 to setOf(4),
            1 to setOf(4),
        )

        val topoOrder = topologicalOrder(graph)

        assertEquals(3, longestPathLength(topoOrder, graph))
    }

}
