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

import algorithms.TarjanSCCFinding.tarjanSCCFinding
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test

class Graphs {
    private val singleRoot = mapOf(1 to setOf(2,3), 2 to setOf(3))
    private val twoRootsLinked = mapOf(1 to setOf(2), 2 to setOf(1))
    private val twoRootsAndOneIndependent = mapOf(
        1 to setOf(2) /* first root */,
        3 /* second root, together with 4 */ to setOf(4, 5), 4 to setOf(3)
    )
    private val lonely = mapOf(1 to setOf<Int>())
    private val loops = mapOf(1 to setOf(2), 2 to setOf(3), 3 to setOf(2))

    @Test
    fun testTarjanSCC() {
        assertEquals(setOf(setOf(1),setOf(2),setOf(3)), tarjanSCCFinding(singleRoot))
        assertEquals(setOf(setOf(1,2)), tarjanSCCFinding(twoRootsLinked))
        assertEquals(setOf(setOf(1), setOf(2),setOf(3,4),setOf(5)), tarjanSCCFinding(twoRootsAndOneIndependent))
        assertEquals(setOf(setOf(1)), tarjanSCCFinding(lonely))
        assertEquals(setOf(setOf(1),setOf(2,3)), tarjanSCCFinding(loops))
    }

    @Test
    fun testRoots() {
        assertEquals(setOf(1), findRoots(singleRoot))
        assertEquals(setOf(1,2), findRoots(twoRootsLinked))
        assertEquals(setOf(1,3,4), findRoots(twoRootsAndOneIndependent))
        assertEquals(setOf(1), findRoots(lonely))
        assertEquals(setOf(1), findRoots(loops))
    }
}
