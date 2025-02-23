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

package analysis

import analysis.type.TypeRewriter
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import testing.ttl.TACMockLanguage
import vc.data.*

class TypeRewriterTest {
  /*  @Test
    fun testRewrite1() {
        val graph = TACMockLanguage.make {
            L1024 = `*`
            K("COND") `=` "L1022 < 0x20"
            L(1022,Tag.Bool) `=` K("COND")
            `if`(1023, "L1022:bool ? 0x1 : 0x0") {
                L1024 = "L1023" // become bool
            } *//* no else case doesn't work? *//* `else` {
                L1021 = `*`
            }
            L1020 = "L1024 == 0x0"
        }
        val coreProgram = CoreTACProgram(
            code = graph.code,
            name = "test",
            blockgraph = graph.toBlockGraph(),
            hooks = TACHooks.empty(),
            procedures = listOf(),
            symbolTable = TACSymbolTable.withTags(
                mapOf(
                TACSymbol.Var("L1024", Tag.Bit256) to Tag.Bit256,
                TACSymbol.Var("L1022", Tag.Bit256) to Tag.Bit256,
                TACSymbol.Var("L1023", Tag.Bit256) to Tag.Bit256,
                TACSymbol.Var("L1021", Tag.Bit256) to Tag.Bit256,
                TACSymbol.Var("L1020", Tag.Bit256) to Tag.Bit256
                )
            ),
            ufAxioms = UfAxioms.empty()
        )
        val fixed = TypeRewriter.fixTypesPostSimplification(coreProgram)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1024)] == null)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1023)] == null)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1022)] == null)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var("L1022bool",Tag.Bool)] == Tag.Bool)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1020)] == null)
    }

    *//*
    @Test
    fun testRewrite2() {
        val graph = TACMockLanguage.make {
            L1024 = `*`
            K("COND") `=` "L1022 < 0x20"
            L(1022,Tag.Bool) `=` K("COND")
            `if`(1023, "L1022:bool ? 0x1 : 0x0") {
                L1024 = "L1023" // become bool
            }
            L1020 = "L1024 == 0x0"
        }
        val coreProgram = CoreTACProgram(
            code = graph.code,
            name = "test",
            blockgraph = graph.toBlockGraph(),
            hooks = TACHooks.empty(),
            procedures = listOf(),
            symbolTable = TACSymbolTable.empty(),
            ufAxioms = UfAxioms.empty()
        )
        val fixed = TypeRewriter.fixTypesPostSimplification(coreProgram)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1024)] == null)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1023)] == null)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1022)] == Tag.Bit256)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var("L1022bool",Tag.Bool)] == Tag.Bool)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1020)] == null)
    }

*//*

    @Test
    fun testRewrite3() {
        val graph = TACMockLanguage.make {
            L1024 = `*`
            K("COND") `=` "L1022 < 0x20"
            L(1022,Tag.Bool) `=` K("COND")
            `if`(L(1022,Tag.Bool)) {
                L1024 = L(1022,Tag.Bool) // become bool
            } *//* no else case doesn't work? *//* `else` {
                L1021 = `*`
            }
            L1020 = "L1024 == 0x0"
        }
        val coreProgram = CoreTACProgram(
            code = graph.code,
            name = "test",
            blockgraph = graph.toBlockGraph(),
            hooks = TACHooks.empty(),
            procedures = listOf(),
            symbolTable = TACSymbolTable.withTags(
                mapOf(
                    TACSymbol.Var("L1024", Tag.Bit256) to Tag.Bit256,
                    TACSymbol.Var("L1022", Tag.Bit256) to Tag.Bit256,
                    TACSymbol.Var("L1023", Tag.Bit256) to Tag.Bit256,
                    TACSymbol.Var("L1021", Tag.Bit256) to Tag.Bit256,
                    TACSymbol.Var("L1020", Tag.Bit256) to Tag.Bit256
                )
            ),
            ufAxioms = UfAxioms.empty()
        )
        val fixed = TypeRewriter.fixTypesPostSimplification(coreProgram)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1024)] == null)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var("L1024bool",Tag.Bool)] == Tag.Bool)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1022)] == null)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var("L1022bool",Tag.Bool)] == Tag.Bool)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1020)] == null)
    }

    *//*
    @Test
    fun testRewrite4() {
        val graph = TACMockLanguage.make {
            L1024 = `*`
            K("COND") `=` "L1022 < 0x20"
            L(1022,Tag.Bool) `=` K("COND")
            `if`(L(1022,Tag.Bool)) {
                L1024 = L(1022,Tag.Bool) // become bool
            }
            L1020 = "L1024 == 0x0"
        }
        val coreProgram = CoreTACProgram(
            code = graph.code,
            name = "test",
            blockgraph = graph.toBlockGraph(),
            hooks = TACHooks.empty(),
            procedures = listOf(),
            symbolTable = TACSymbolTable.empty(),
            ufAxioms = UfAxioms.empty()
        )
        val fixed = TypeRewriter.fixTypesPostSimplification(coreProgram)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1024)] == Tag.Bit256)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var("L1024bool",Tag.Bool)] == Tag.Bool)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1022)] == Tag.Bit256)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var("L1022bool",Tag.Bool)] == Tag.Bool)
        Assertions.assertTrue(fixed.symbolTable.tags[TACSymbol.Var.stackVar(1020)] == null)
    }
     *//*
*/}
