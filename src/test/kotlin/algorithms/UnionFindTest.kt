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

import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test

internal class UnionFindTest {

    fun check(uf : EquivalenceRelation<Int>) {
        assertTrue(uf.areEqual(1, 3))
        assertTrue(uf.areEqual(3, 2))
        assertTrue(uf.areEqual(6, 5))
        assertTrue(!uf.areEqual(10, 1))
        assertTrue(!uf.areEqual(5, 10))

        assertTrue(uf.getEquivalenceClass(3) == setOf(1, 2, 3, 4))
        assertTrue(uf.getEquivalenceClass(5) == setOf(5, 6))
        assertTrue(uf.getEquivalenceClass(10) == setOf(10))
        assertTrue(uf.getAllEquivalenceClasses() == setOf(setOf(1, 2, 3, 4), setOf(5, 6), setOf(10)))
    }

    @Test
    fun testStuff() {
        val uf = UnionFind<Int>()

        uf.union(1, 2)
        uf.union(2, 3)
        uf.union(1, 4)
        uf.union(5, 6)
        uf.register(10)
        uf.union(5, 6)
        check(uf)
        check(uf.toImmutable())
    }
}