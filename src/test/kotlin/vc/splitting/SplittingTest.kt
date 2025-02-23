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

package vc.splitting

import config.Config
import config.ConfigScope
import loaders.WithTACSource
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Assertions.assertFalse
import org.junit.jupiter.api.Test
import vc.data.CoreTACProgram
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import verifier.autoconfig.AutoConfigManager
import verifier.splits.SplitTree

class SplittingTest : WithTACSource, TACBuilderAuxiliaries() {

    private fun size(s: SplitTree.Node) =
        s.generate(AutoConfigManager("test")).blockgraph.keys.size

//    private fun printGraph(s: Split) {
//        val g = s.generate().blockgraph
//        println()
//        for (v in g.keys) {
//            println("$v -> ${g[v]}")
//        }
//        println()
//    }

    private fun splitOfSplits(prog: CoreTACProgram, depth: Int) =
        SplitTree(prog, Config.Smt.SplittingDepth).rootNode.let { root ->
            (0..<depth).runningFold(listOf(root)) { splits, _ ->
                splits.flatMap {
                    val tac = it.generate(AutoConfigManager("test"))
                    if (it.splittable) {
                        it.split(tac)
                    } else {
                        listOf(it)
                    }
                }
            }
        }

    @Test
    fun test01() {
        val prog = this.loadTACProgramResource("vc/splitting/a.tac")
        val root = SplitTree(prog, Config.Smt.SplittingDepth).rootNode
        assertFalse(root.getSplittableAnyway(AutoConfigManager("SplittingTest")))
    }

    @Test
    fun test02() {
        val prog = this.loadTACProgramResource("vc/splitting/b.tac")
        val root = SplitTree(prog, Config.Smt.SplittingDepth).rootNode
        val tac = root.generate(AutoConfigManager("SplittingTest"))
        val splits = root.split(tac)
        val splitsSizes = splits.map(::size)
        assertEquals(setOf(3, 5), splitsSizes.toSet())
    }

    @Test
    fun test03() {
        val prog = this.loadTACProgramResource("vc/wp/Rule-Invertibility.tac")
        val splits = splitOfSplits(prog, 2)
        val splitsSizes = splits[2].map(::size)
        assertEquals(setOf(13, 16, 19), splitsSizes.toSet())
    }


    /**
     * two tests trying more complicated cfgs
     * e.g. trying to represent something like
     * if (c) {
     *      if (c1)  { ... ; return; }
     *      if (c2) { ... ; return; }
     * }
     *
     * if (d) {
     *      return;
     * }
     * ...
     */
    @Test
    fun test04() {
        ConfigScope(Config.OptimizeAfterSplits , 0).use {
            val prog = this.loadTACProgramResource("vc/splitting/c.tac")
            val results = splitOfSplits(prog, 6)
            assertEquals(listOf(1, 2, 4, 8, 16, 24, 24), results.map { it.size })
        }
    }

    @Test
    fun test05() {
        ConfigScope(Config.OptimizeAfterSplits , 0).use {
            val prog = this.loadTACProgramResource("vc/splitting/d.tac")
            val results = splitOfSplits(prog, 6)
            assertEquals(listOf(1, 2, 4, 8, 12, 16, 16), results.map { it.size })
        }
    }

    @Test
    fun test06() {
        val prog = this.loadTACProgramResource("vc/splitting/e.tac")
        val results = splitOfSplits(prog, 2)
        assertEquals(listOf(1, 2, 2), results.map { it.size })
    }

    @Test
    fun testNonLinear() {
        val prog = TACProgramBuilder {
            nop
            jump(1) {
                jump(3) {
                    a assign Mul(bS, cS)
                    jump(100) {
                        assert(False)
                    }
                }
                jump(4) {
                    a assign Mul(bS, cS)
                    jump(100)
                }
            }
            jump(2) {
                jump(5) {
                    jump(100)
                }
                jump(6) {
                    jump(100)
                }
            }
        }
        val root = SplitTree(prog.code, Config.Smt.SplittingDepth).rootNode
        val tac = root.generate(AutoConfigManager("test"))
        val (s1, _) = root.split(tac)
        assertEquals(setOf(prog.block(4)), s1.address.mustPass())
    }

}
