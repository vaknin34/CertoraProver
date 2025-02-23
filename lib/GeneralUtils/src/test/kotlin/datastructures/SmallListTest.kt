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

package datastructures

import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions.*


class SmallListTest {
    @Test
    fun simple() {
        assertEquals(listOf<Int>(), SmallList.Of0<Int>())
        assertEquals(listOf(1), SmallList.Of1(1))
        assertEquals(listOf(1, 2), SmallList.Of2(1, 2))
        assertEquals(listOf(1, 2, 3), SmallList.Of3(1, 2, 3))
        assertEquals(listOf(1, 2, 3, 4), SmallList.Of4(1, 2, 3, 4))
        assertEquals(listOf(1, 2, 3, 4, 5), SmallList.Of5(1, 2, 3, 4, 5))

        for (l in listOf(
            SmallList.Of1(1),
            SmallList.Of2(1, 2),
            SmallList.Of3(1, 2, 3),
            SmallList.Of4(1, 2, 3, 4),
            SmallList.Of5(1, 2, 3, 4, 5)
        )) {
            for (i in 0..<l.size) {
                assertEquals(i + 1, l[i])
            }
        }
    }

    @Test
    fun notEqual() {
        assertNotEquals(listOf(1), SmallList.Of2(1, 2))
        assertNotEquals(listOf(1), SmallList.Of1(2))
        assertNotEquals(listOf(1, 2), SmallList.Of1(1))
        assertNotEquals(listOf(1, 2), SmallList.Of2(2, 1))
    }

    @Test
    fun iteration() {
        assertEquals(listOf(1, 2, 3, 4, 5), SmallList.Of5(1, 2, 3, 4, 5).asSequence().toList())
        assertEquals(listOf(1), SmallList.Of1(1).asSequence().toList())
        assertEquals(listOf<Int>(), SmallList.Of0<Int>().asSequence().toList())
    }

    @Test
    fun subList() {
        val l = listOf(1, 2, 3, 4)
        assertEquals(listOf(1, 2), l.subList(0, 2))
        assertEquals(listOf(3), l.subList(2, 3))
        assertEquals(listOf(3, 4), l.subList(2, 4))
        assertEquals(listOf<Int>(), l.subList(2, 2))
        assertEquals(2, l.subList(1, 3).size)
        assertEquals(4, l.subList(2, 4)[1])
    }

    @Test
    fun indexOf() {
        val l = SmallList.Of5(1, 1, 2, 3, 3)
        assertEquals(0, l.indexOf(1))
        assertEquals(2, l.indexOf(2))
        assertEquals(3, l.indexOf(3))
        assertEquals(-1, l.indexOf(4))
        assertEquals(1, l.lastIndexOf(1))
        assertEquals(2, l.lastIndexOf(2))
        assertEquals(4, l.lastIndexOf(3))
        assertEquals(-1, l.lastIndexOf(4))
    }


    @Test
    fun containsAll() {
        val l = SmallList.Of5(1, 1, 2, 3, 3)
        assertTrue(l.containsAll(listOf(1, 2, 3)))
        assertTrue(l.containsAll(listOf(1, 2)))
        assertTrue(l.containsAll(listOf(3)))
        assertTrue(l.containsAll(listOf<Int>()))
        assertFalse(l.containsAll(listOf(1, 2, 3, 4)))
        assertFalse(l.containsAll(listOf(4)))
    }
}
