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

// TODO CVL REWRITE : RE-ENABLE CER-1493

/*
class TypeCheckerTest {
    private val sortsInScope = 25.downTo(1).map { n ->
        Tag.UserDefined.UninterpretedSort("sort$n")
    }
    private val varsInScope = sortsInScope.mapIndexed { n, sort ->
        TACSymbol.Var("goodvar$n", sort)
    }
    private val sortsOutOfScope = 10.downTo(1).map { n ->
        Tag.UserDefined.UninterpretedSort("badboi$n")
    }
    private val varsOutOfScope = sortsOutOfScope.mapIndexed { n, sort ->
        TACSymbol.Var("badvar$n", sort)
    }
    private val functions = mapOf(
        "fun1" to FunctionInScope.UF(
            "fun1",
            listOf(Tag.Int, Tag.Int),
            sortsInScope[0]
        ),
        "fun2" to FunctionInScope.UF(
            "fun2",
            listOf(Tag.Bool, Tag.Bit256, Tag.Int),
            Tag.Bool
        ),
        "fun3" to FunctionInScope.UF(
            "fun3",
            listOf(Tag.ByteMap, Tag.Int),
            Tag.Int
        ),
        "fun4" to FunctionInScope.UF(
            "fun4",
            listOf(Tag.ByteMap, Tag.Int),
            Tag.Int
        )
    )
    private val symbolTable = TACSymbolTable(sortsInScope.toSet(), functions.values.toSet(), setOf(), emptyTags())
    private val typeChecker = TypeChecker(symbolTable)

    @TestFactory
    fun badExpressions() =
        listOf(
            TACExpr.BinRel.Eq(varsOutOfScope[1].asSym(), varsOutOfScope[1].asSym()) to "using undeclared sorts",
            TACExpr.Select.buildMultiDimSelect(
                TACSymbol.Var("badfun", Tag.Bit256).asSym(),
                listOf(TACSymbol.Const(5.toBigInteger()).asSym())
            ) to "applying undeclared function",
            TACExpr.Select.buildMultiDimSelect(
                TACSymbol.Var("fun1", functions["fun1"]!!.asTag).asSym(),
                listOf(TACSymbol.True.asSym(), TACSymbol.Const(10.toBigInteger()).asSym()),
            ) to "passing bad parameters",
            TACExpr.UnaryExp.BWNot(TACExpr.BinRel.Eq(TACSymbol.Const(5.toBigInteger()).asSym(),
                    TACSymbol.Const(5.toBigInteger()).asSym()))
                    to "BWNot params don't type check"
        )
            .map { (expr, summary) ->
                DynamicTest.dynamicTest("when I check $expr ($summary) I get TACExprTag.Error") {
                    Assertions.assertTrue(typeChecker.typeCheck(expr) is TypeCheckerResult.Error)
                }
            }

        @TestFactory
        fun badExpressionException() =
                listOf(TACExpr.UnaryExp.BWNot(TACExpr.BinRel.Eq(TACSymbol.Const(5.toBigInteger()).asSym(),
                        TACSymbol.Const(5.toBigInteger()).asSym()))
                        to "BWNot params don't type check"

                ).map { (expr, summary) ->
                    DynamicTest.dynamicTest( "when I check $expr ($summary) I get a TypeCheckerException") {
                        val node = StartBlock.copy(origStartPc = 0)
                        val block = listOf(TACCmd.Simple.AssigningCmd.AssignExpCmd(TACSymbol.Var("x", Tag.Bit256), expr))
                        val blockNodes = mapOf(node to block)
                        val blockGraph = mapOf<NBId, Set<NBId>>(node to setOf())
                        Assertions.assertThrows(TACTypeCheckerException::class.java) {
                            TypeChecker.checkProgram(CoreTACProgram(blockNodes, blockGraph, "test",
                                    TACSymbolTable.empty(), InstrumentationTAC(UfAxioms.empty(), TACHooks.empty(), setOf()), setOf(), true))
                        }
                    }
                }

    @TestFactory
    fun goodExpressions() =
        listOf(
            TACExpr.BinRel.Eq(varsInScope[0].asSym(), varsInScope[0].asSym()) to TACExprTag.Bool,
            TACExpr.Select.buildMultiDimSelect(
                TACSymbol.Var("fun1", functions["fun1"]!!.asTag).asSym(),
                listOf(
                    TACSymbol.Const(5.toBigInteger()).asSym(),
                    TACSymbol.Var("test_var", Tag.Bit256).asSym()
                ),
            ) to TACExprTag(sortsInScope[0])
        )
            .map { (expr, type) ->
                DynamicTest.dynamicTest("when I check $expr the checker succeeds and returns $type") {
                    Assertions.assertEquals(type, (typeChecker.typeCheck(expr) as? TypeCheckerResult.Result)?.result?.tag)
                }
            }
}
*/
