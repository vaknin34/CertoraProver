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

package verifier

import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import utils.SimplePair
import utils.mapToSet
import verifier.splits.DAGSplitter
import verifier.splits.SizeSideScore
import verifier.splits.SplitScorer
import verifier.splits.cutDAG

class DAGSplitterTest {

    /** Practically the same as [SizeScorer], but not for blocks, but where vertices are ints. */
    private val simpleScorer = object : SplitScorer<Int, SizeSideScore> {
        override fun ofOne(v: Int) = SizeSideScore(1)

        private val SimplePair<SizeSideScore>.value
            get() = first.blocks.toLong() * second.blocks.toLong()

        override fun comparePair(p1: SimplePair<SizeSideScore>, p2: SimplePair<SizeSideScore>) =
            p1.value.compareTo(p2.value)
    }

    @Test
    fun test1() {
        val graph = buildMap {
            fun Int.add(vararg children: Int) {
                this@buildMap[this] = children.toSet()
            }
            1.add(2, 3)
            2.add(4)
            3.add(4)
            4.add()
        }
        val splitter = DAGSplitter(graph, origSinks = setOf(1))
        assertTrue(splitter.isSplittable())
        assertEquals(setOf(2, 3), splitter.bestPivots(simpleScorer).first.mapToSet { it.pivot })
    }

    @Test
    fun test2() {
        val graph = buildMap {
            fun Int.add(vararg children: Int) {
                this@buildMap[this] = children.toSet()
            }
            1.add(2, 3)
            2.add(4)
            3.add(4)
            4.add(5)
            5.add()
        }
        val splitter = DAGSplitter(graph, origSinks = setOf(2, 3))
        assertTrue(splitter.isSplittable())
        assertEquals(setOf(2, 3), splitter.bestPivots(simpleScorer).first.mapToSet { it.pivot })
    }

    @Test
    fun test3() {
        val graph = buildMap {
            fun Int.add(vararg children: Int) {
                this@buildMap[this] = children.toSet()
            }
            1.add(2)
            2.add(3)
            3.add(4)
            4.add()
        }
        val splitter = DAGSplitter(graph, origSinks = setOf())
        assertFalse(splitter.isSplittable())
    }

    @Test
    fun testDAGCutter() {
        val g = mutableMapOf<Int, Set<Int>>().apply {
            fun x(x: Int, vararg succs: Int) {
                this[x] = succs.toSet()
            }
            x(0, 1, 2)
            x(1, 3)
            x(2, 3, 10)
            x(3, 4, 5)
            x(4, 6, 8)
            x(5, 6, 7)
            x(6, 8)
        }
        val res = cutDAG(
            root = 0,
            origGraph = g,
            mustPass = setOf(3, 6),
            dontPass = setOf(2),
            origSinks = setOf(8, 10)
        )
        val expected = mutableMapOf<Int, Set<Int>>().apply {
            fun x(x: Int, vararg succs: Int) {
                this[x] = succs.toSet()
            }
            x(0, 1)
            x(1, 3)
            x(3, 4, 5)
            x(4, 6)
            x(5, 6)
            x(6, 8)
            x(8)
        }
        assertEquals(expected, res)
    }
}
