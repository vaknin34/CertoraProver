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

package analysis.integeroverflows

import analysis.opt.overflow.OverflowPatternRewriter.Companion.OverflowMetaData
import analysis.opt.overflow.OverflowPatternRewriter.Companion.overflowMeta
import analysis.opt.overflow.RecipeType
import annotation.SolidityVersion
import datastructures.stdcollections.*
import infra.CVLFlow
import infra.CertoraBuild.Companion.EVMCompiler
import infra.CertoraBuild.Companion.solcOptimize
import infra.CertoraBuild.Companion.viaIR
import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.assertEquals
import report.DummyLiveStatsReporter
import rules.CompiledRule
import solver.SolverResult
import utils.*
import utils.Color.Companion.black
import utils.Color.Companion.blueBg
import vc.data.CoreTACProgram
import vc.data.TACExpr
import verifier.TACVerifier
import verifier.Verifier

object OverflowTestAux {

    private val solcVersions = listOf(
        SolidityVersion.V8_2, SolidityVersion.V8_9, SolidityVersion.V8_11,
        SolidityVersion.V8_13, SolidityVersion.V8_16, SolidityVersion.V8_19,
        SolidityVersion.V8_27
    ).map { EVMCompiler.Solidity(it.compilerName()) }

    val vyperVersions = listOf(
        // Earlier version of vyper don't support types other than int128 and uint256.
        //"vyper0.3.4", vyper is so slow we're going to skip this one.
        "vyper0.3.10",
    ).map { EVMCompiler.Vyper(it) }

    /** our tool crashes on solc8.2 with IR. is there a ticket? */
    private val noIRsupport = listOf(SolidityVersion.V8_2).map { it.compilerName() }

    private fun viaIrOptions(compiler: EVMCompiler) =
        if (compiler.isVyper || compiler.cmd in noIRsupport) {
            setOf(false)
        } else {
            setOf(false, true)
        }

    private inline fun CoreTACProgram.countE(p: (TACExpr) -> Boolean) =
        analysisCache.graph.commands.flatMap { it.cmd.subExprs() }.count(p)

    fun isMathintOutOfRangeCVLText(expr: String, signed: Boolean, width: Int) =
        if (signed) {
            "$expr > ${SignUtilities.maxSignedValueOfBitwidth(width)} || " +
                "$expr < ${SignUtilities.minSignedValueOfBitwidth(width)}"
        } else {
            "$expr > ${SignUtilities.maxUnsignedValueOfBitwidth(width)} || $expr < 0"
        }

    fun runContractAndSpec(
        contract: String,
        spec: String,
        compiler: EVMCompiler,
        withOptimize: Boolean,
        withViaIR: Boolean,
    ): Verifier.JoinedResult {
//        println(contract)
//        println()
//        println(spec)
//        println()
        val flow = CVLFlow()
        val pqAndS = flow.getProverQueryWithScene(
            contract = contract,
            cvlText = spec,
            compiler = compiler,
            buildConf = {
                solcOptimize(withOptimize)
                viaIR(withViaIR)
            }
        )
        pqAndS.errorOrNull()?.let {
            error(it.toString())
        }
        val (scene, tacs) = flow.transformResultsToTACs(pqAndS)
        val tac = tacs.find { it.tac.name == "test" }
            ?: error("failed to find tac named test, got: ${tacs.map { it.tac.name }}")

        val optimizedTac = CompiledRule.optimize(scene.toIdentifiers(), tac.tac)
        return runBlocking {
            Verifier.JoinedResult(TACVerifier.verify(scene.toIdentifiers(), optimizedTac, DummyLiveStatsReporter))
        }
    }


    data class TestConfig(
        val compiler: EVMCompiler,
        val signed: Boolean,
        val optimize: Boolean,
        val viaIR: Boolean,
        val withRevert: Boolean,
        val width: Int
    ) {
        val baseType = ite(signed, "int", "uint")
        val type = "$baseType$width"
        val isVyper = compiler.isVyper

        fun test(
            specAndContract: Pair<String, String>,
            checkFinalTac: (Pair<CoreTACProgram, String>) -> Unit,
            msg: String = this.toString(),
        ) {
//            println("Start : $msg".blueBg.black)
            val (spec, contract) = specAndContract
            val verifierResult = runContractAndSpec(
                contract = contract,
                spec = spec,
                compiler = compiler,
                withOptimize = optimize,
                withViaIR = viaIR,
            )
            checkFinalTac(verifierResult.simpleSimpleSSATAC to msg)
            assertEquals(SolverResult.UNSAT, verifierResult.finalResult, msg)
//            println("End : $msg".blueBg.black)
        }

        private fun toMeta(recipeType: RecipeType) = OverflowMetaData(recipeType, width, signed)
        val binMulMeta get() = toMeta(RecipeType.BinaryMul)
        val additionMeta get() = toMeta(RecipeType.Add)
        val subtractionMeta get() = toMeta(RecipeType.Sub)
    }


    fun TestConfig.simpleBinarySpecAndContract(op: String): Pair<String, String> {
        val contract = when {
            isVyper ->
                """
                    |@external
                    |def testFunc(x: $type, y: $type) -> ${type}:
                    |   return x $op y
                """

            else ->
                """
                    |contract test {
                    |   function testFunc($type x, $type y) external returns ($type) {
                    |       return x $op y;
                    |   }
                    |}
                    """
        }.trimMargin()

        val spec =
            if (!withRevert) {
                """
                    |rule test(env e, $type x, $type y) {
                    |   assert testFunc(e, x, y) == assert_$type(x $op y);
                    |}
                    """
            } else {
                """
                    |rule test(env e, $type x, $type y) {
                    |   require e.msg.value == 0;
                    |   mathint mathintRes = x $op y;
                    |   $type contractRes = testFunc@withrevert(e, x, y);
                    |   if (lastReverted) {
                    |      assert ${isMathintOutOfRangeCVLText("mathintRes", signed, width)};
                    |   } else {
                    |      assert contractRes == assert_$type(mathintRes);
                    |   }
                    |}
                """
            }.trimMargin()

        return spec to contract
    }


    fun checkMul(progAndMsg: Pair<CoreTACProgram, String>, vararg expectedRewrites: OverflowMetaData) {
        val (c, msg) = progAndMsg
        assertEquals(
            0,
            c.countE { it is TACExpr.BinOp.Div || it is TACExpr.BinOp.SDiv },
            "remaining divs : $msg"
        )
        assertEquals(
            0,
            c.countE { it is TACExpr.BinOp.ShiftRightLogical || it is TACExpr.BinOp.ShiftRightArithmetical },
            "remaining shifts : $msg"
        )
        checkRewrites(progAndMsg, *expectedRewrites)
    }

    fun checkAdd(progAndMsg: Pair<CoreTACProgram, String>, vararg expectedRewrites: OverflowMetaData) {
        val (c, msg) = progAndMsg
        assertEquals(
            0,
            c.countE { it is TACExpr.Vec.Add },
            "remaining adds : $msg"
        )
        checkRewrites(progAndMsg, *expectedRewrites)
    }

    fun checkSub(progAndMsg: Pair<CoreTACProgram, String>, vararg expectedRewrites: OverflowMetaData) {
        val (c, msg) = progAndMsg
        assertEquals(
            0,
            c.countE { it is TACExpr.BinOp.Sub },
            "remaining subs : $msg"
        )
        checkRewrites(progAndMsg, *expectedRewrites)
    }


    private fun checkRewrites(progAndMsg: Pair<CoreTACProgram, String>, vararg expectedRewrites: OverflowMetaData) {
        val (c, msg) = progAndMsg
        val actual = c.analysisCache.graph.commands.mapNotNull { it.cmd.meta[overflowMeta] }.toList()
        val expected = expectedRewrites.toList()
        // the groupBy is to account for multiplicity in rewrites.
        assertEquals(
            expected.groupBy { it }.mapValues { it.value.size },
            actual.groupBy { it }.mapValues { it.value.size },
            "different rewrites : $msg"
        )
    }

    fun configSequence(vararg widths: Int) = sequence {
        for (compiler in solcVersions + vyperVersions) {
            for (signed in setOf(false, true)) {
                for (optimize in setOf(false, true)) {
                    for (viaIR in viaIrOptions(compiler)) {
                        for (withRevert in setOf(false, true)) {
                            for (width in widths) {
                                yield(TestConfig(compiler, signed, optimize, viaIR, withRevert, width))
                            }
                        }
                    }
                }
            }
        }
    }

}
