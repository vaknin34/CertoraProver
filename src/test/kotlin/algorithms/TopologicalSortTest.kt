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

import datastructures.add
import datastructures.mutableMultiMapOf
import datastructures.pairs
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import kotlin.random.Random

internal class TopologicalSortTest {

    @Test
    fun topTest() {
        val g = mutableMultiMapOf<Int, Int>()
        val random = Random(1)
        repeat(200) {
            val x = random.nextInt(100)
            val y = random.nextInt(x + 1, 101)
            g.add(x, y)
        }
        val order = topologicalOrder(g).toList()
        assertEquals(order.size, order.distinct().size)
        val reversed = order.indices.associateBy { order[it] }
        for ((i, j) in g.pairs) {
            assertTrue(reversed[i]!! > reversed[j]!!)
        }

        g.add(75, 3)
        g.add(3, 30)
        g.add(30, 75)
        assertEquals(null, topologicalOrderOrNull(g))
    }

    @Test
    fun selfLoopTest() {
        val g = mutableMultiMapOf<Int, Int>()
        g.add(1, 3)
        g.add(3, 3)
        g.add(3, 5)
        assertEquals(null, topologicalOrderOrNull(g))
    }

}
