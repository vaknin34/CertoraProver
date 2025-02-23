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

package analysis.icfg

import annotation.SolidityVersion
import annotation.SolidityVersions
import annotations.TestTags
import loaders.SoliditySceneTest
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.BeforeAll
import org.junit.jupiter.params.ParameterizedTest
import solver.SolverResult
import tac.Tag
import vc.data.*
import vc.data.TACCmd.Simple
import java.math.BigInteger
import org.junit.jupiter.api.Tag as TestTag

@TestTag(TestTags.EXPENSIVE) // comment this line if you need to run any of these tests locally
class InlinerTest : SoliditySceneTest {
    companion object : SoliditySceneTest {
        private val scenes = mutableMapOf<String, InlinerTestUtils.InsertMethodData>()
        private val solidityVersions =
            listOf(SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13)

        @JvmStatic
        @BeforeAll
        fun beforeAll() {
            for (sv in solidityVersions) {
                val solc = "solc" + sv.pointSuffix
                scenes.put(solc, InlinerTestUtils.preloadTest(solc))
            }
        }
    }

    private fun loadTest(solc: String): InlinerTestUtils.InsertMethodData {
        return scenes[solc]!!
    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
    fun testInsertMethodCallConstantReturn(solc: String) {
        val testData = loadTest(solc)
        val res = InlinerTestUtils.insertAndRun(testData, listOf(testData.viewConstant), {
                patching, where, callParams -> with(patching) {
                assertEquals(callParams.size, 1)
                val viewCallParams = callParams.first()
                val assertVar = TACSymbol.Var("testAssertVar", Tag.Bool)
                val selectVar = TACSymbol.Var("testSelectVar", Tag.Bit256)
                val returnBuffer = viewCallParams.returnBuffer

                addVarDecls(setOf(assertVar, selectVar, returnBuffer))
                replaceCommand(
                    where, listOf(
                        Simple.AssigningCmd.AssignExpCmd(
                            selectVar,
                            TACExpr.Select(returnBuffer.asSym(), 0.asTACExpr)
                        ),
                        Simple.AssigningCmd.AssignExpCmd(
                            assertVar,
                            TACExpr.BinRel.Eq(
                                selectVar.asSym(),
                                BigInteger.valueOf(100).asTACExpr
                            )
                        ),
                        Simple.AssertCmd(assertVar, "View function result should equal 100"),
                    )
                )
            }
        })

        assertTrue(res.finalResult == SolverResult.UNSAT)
    }


    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
    fun testInsertTwoDifferentMethodSameCalldata(solc: String) {
        // The functions should be sometimes different and sometimes equal. So I should check for both Eq and Not(Eq)
        // and see SAT
        val testData = loadTest(solc)
        val functionsToCall = listOf(testData.viewConstant, testData.twoParams)
        InlinerTestUtils.runSameInputDifferentOutput(testData, functionsToCall[0], functionsToCall[1])

        val res2 = InlinerTestUtils.insertAndRun(
            testData,
            functionsToCall,
            preambleCreator = InlinerTestUtils.inputEqualityInstrumentor(0, 1),
            assertionCreator = InlinerTestUtils.outputInequalityInstrumentor(0, 1, true)
        )
        assertTrue(res2.finalResult == SolverResult.SAT)
    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
    fun testUpdateMemoryReturn(solc: String) {
        val testData = loadTest(solc)
        InlinerTestUtils.runSanity(testData, testData.updateBookTitle)
        InlinerTestUtils.runDifferentInputDifferentOutput(testData, testData.updateBookTitle, testData.updateBookTitle)
        // TODO: Can't support comparing memory at the moment. Memory is part of the output, so I can't test the output
        //  is equal.
        //  I think the output size have been equal between two separate calls. This is because we don't support
        //  changing the input for the second call for now.
        //  Test is unsupported for now.
//        runSameInputSameOutput(testData, testData.updateBookTitle, testData.updateBookTitle)
    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
    fun testFunctionWithStructMemroy_BookId(solc: String) {
        val testData = loadTest(solc)
        InlinerTestUtils.runSanity(testData, testData.getBookId)
        InlinerTestUtils.runSanity(testData, testData.updateBookId)
        InlinerTestUtils.runDifferentInputDifferentOutput(testData, testData.getBookId, testData.getBookId)
        InlinerTestUtils.runSameInputSameOutput(testData, testData.getBookId, testData.getBookId)
    }

    // TODO: Currently not supported. Return when supported
    // getBookId -> getUpdateBookId -> getBookId
//    @ParameterizedTest
//    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
//    fun testUpdateMemoryAndCallAgain(solc: String) {
//        val testData = loadTest(solc)
//        val res = insertAndRun(testData, listOf(testData.getBookId, testData.updateBookId, testData.getBookId),
//            preambleCreator = {where, patching, callParams ->
//                createInputEquality(0, 1)(where, patching, callParams)
//                createInputEquality(1, 2)(where, patching, callParams)
//            },
//            assertionCreator = createOutputNotEqual(0, 2, false)
//        )
//        // TODO: Read up about memory to understand what is the expected behaviour
//        assertEquals(SolverResult.UNSAT, res.finalResult) {"Model: ${res.firstExampleInfo.model}"}
//    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
    fun testViewTupleAndAddress_getBalance(solc: String) {
        val testData = loadTest(solc)
        InlinerTestUtils.runSanity(testData, testData.getBalance)
        InlinerTestUtils.runDifferentInputDifferentOutput(testData, testData.getBalance, testData.getBalance)
        InlinerTestUtils.runSameInputSameOutput(testData, testData.getBalance, testData.getBalance)
    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
    fun testViewTwoBasicParams_twoParams(solc: String) {
        val testData = loadTest(solc)
        InlinerTestUtils.runSanity(testData, testData.twoParams)
        InlinerTestUtils.runDifferentInputDifferentOutput(testData, testData.twoParams, testData.twoParams)
        InlinerTestUtils.runSameInputSameOutput(testData, testData.twoParams, testData.twoParams)
    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
    fun testBoolean_lnot(solc: String) {
        val testData = loadTest(solc)
        InlinerTestUtils.runSanity(testData, testData.lnot)
        InlinerTestUtils.runDifferentInputDifferentOutput(testData, testData.lnot, testData.lnot)
        InlinerTestUtils.runSameInputSameOutput(testData, testData.lnot, testData.lnot)
    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
    fun testBooleanSemantics_lnot(solc: String) {
        val testData = loadTest(solc)
        val res = InlinerTestUtils.insertAndRun(testData, listOf(testData.lnot), { patching, where, callParams ->
            with(patching) {
                assertEquals(callParams.size, 1)
                val viewCallParams = callParams.first()
                val assertVar = TACSymbol.Var("testAssertVar", Tag.Bool)
                val selectVar = TACSymbol.Var("testSelectVar", Tag.Bit256)
                val selectInVar = TACSymbol.Var("testSelectInVar", Tag.Bit256)
                val returnBuffer = viewCallParams.returnBuffer

                addVarDecls(setOf(assertVar, selectVar, returnBuffer, selectInVar))
                replaceCommand(
                    where, listOf(
                        Simple.AssigningCmd.AssignExpCmd(
                            selectVar,
                            TACExpr.Select(returnBuffer.asSym(), 0.asTACExpr)
                        ),
                        Simple.AssigningCmd.AssignExpCmd(
                            selectInVar,
                            // 4 is index where the input will be (after the selector)
                            TACExpr.Select(viewCallParams.inputMem.asSym(), 4.asTACExpr)
                        ),
                        Simple.AssigningCmd.AssignExpCmd(
                            assertVar,
                            TACExpr.UnaryExp.LNot(
                                TACExpr.BinRel.Eq(
                                    selectVar.asSym(),
                                    selectInVar.asSym()
                                )
                            )
                        ),
                        Simple.AssertCmd(assertVar, "LNot should negate the value"),
                    )
                )
            }
        })

        assertTrue(res.finalResult == SolverResult.UNSAT)
    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
    fun testInsertViewMemoryArgs(solc: String) {
        val testData = loadTest(solc)
        InlinerTestUtils.runSanity(testData, testData.viewMemoryArg)
        InlinerTestUtils.runDifferentInputDifferentOutput(testData, testData.viewMemoryArg, testData.viewMemoryArg)
        InlinerTestUtils.runSameInputSameOutput(testData, testData.viewMemoryArg, testData.viewMemoryArg)
    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
    fun testViewByParamAndState_swag(solc: String) {
        val testData = loadTest(solc)
        InlinerTestUtils.runSanity(testData, testData.swag)
        InlinerTestUtils.runDifferentInputDifferentOutput(testData, testData.swag, testData.swag)
        InlinerTestUtils.runSameInputSameOutput(testData, testData.swag, testData.swag)
    }

    // TODO: Currently not supported. Return when supported
//    @ParameterizedTest
//    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
//    fun testInsertStateChanges(solc: String) {
//        val testData = loadTest(solc)
//
//        val functionsToCall = listOf(testData.getFoo, testData.blazeit, testData.getFoo)
//        // inline blazeit which will at least double foo. Save foo before, then check foo again after.
//        val res = insertAndRun(testData, functionsToCall, { patching, where, callParams ->
//            val fooParams1 = callParams[0]
//            val fooParams2 = callParams[2]
//            val blazeitParams = callParams[1]
//            val assertVar = TACSymbol.Var("assertVar", Tag.Bool)
//            with(patching) {
//                addVarDecl(assertVar)
//                replaceCommand(
//                    where, listOf(
//                        Simple.AssumeNotCmd(blazeitParams.lastReverted),
//                        Simple.AssigningCmd.AssignExpCmd(
//                            assertVar, TACExpr.BinRel.Le(
//                                TACExpr.Vec.Mul(
//                                    2.asTACExpr,
//                                    TACExpr.Select(fooParams1.returnBuffer.asSym(), 0.asTACExpr)
//                                ),
//                                TACExpr.Select(fooParams2.returnBuffer.asSym(), 0.asTACExpr)
//                            )
//                        ),
//                        Simple.AssertCmd(assertVar, "Foo should be at least doubled after blazeit")
//                    )
//                )
//            }
//        })
//        assertEquals(res.finalResult, SolverResult.UNSAT)
//    }

    // TODO: Currently not supported. Return when supported
//    @ParameterizedTest
//    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
//    fun testRecursionFunction(solc: String) {
//        val testData = loadTest(solc)
//        val functionToCall = testData.recurse10
//        // TODO: turn off recursion protection
//        runSanity(testData, functionToCall)
//        // TODO: other tests
//    }

    @ParameterizedTest
    @SolidityVersions([SolidityVersion.V5_16, SolidityVersion.V6_12, SolidityVersion.V7_6, SolidityVersion.V8_13])
    fun testLoopFunction(solc: String) {
        val testData = loadTest(solc)
        val functionToCall = testData.loopTimes10
        InlinerTestUtils.runSanity(testData, functionToCall)
        InlinerTestUtils.runDifferentInputDifferentOutput(testData, testData.loopTimes10, testData.loopTimes10)
        InlinerTestUtils.runSameInputSameOutput(testData, testData.loopTimes10, testData.loopTimes10)
    }
}
