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

package analysis.abi

import analysis.icfg.Inliner
import analysis.icfg.Inliner.CallStack.STACK_PUSH
import analysis.maybeAnnotation
import annotation.ScopedMatrix
import config.Config
import extension.DependentPair
import extension.setTo
import kotlin.collections.listOf
import kotlinx.coroutines.runBlocking
import loaders.SoliditySceneTest
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.params.ParameterizedTest
import scene.IScene
import scene.Scene
import utils.mapNotNull
import vc.data.CoreTACProgram
import java.math.BigInteger
import java.util.stream.Collectors

abstract class DirectPassingTest : SoliditySceneTest {
    abstract val header: String

    @ParameterizedTest
    @ScopedMatrix
    fun testNestedDynamic(solc: String) {
        this.runTestPipeline("analysis/abi/NestedDynamic.sol", solc, 1) {
            solc
        }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testNestedStatic(solc: String) {
        this.runTestPipeline("analysis/abi/NestedStatic.sol", solc, 1) {
            solc
        }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testA(solc: String) {
        this.runTestPipeline("analysis/abi/A.sol", solc, 1) { solc }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testC(solc: String) {
        this.runTestPipeline("analysis/abi/C.sol", solc, 1) { solc }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testE(solc: String) {
        this.runTestPipeline("analysis/abi/E.sol", solc, 1) { solc }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testF(solc: String) {
        this.runTestPipeline("analysis/abi/F.sol", solc, 3) { solc }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testG(solc: String) {
        this.runTestPipeline("analysis/abi/G.sol", solc, 3) { solc }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testG2(solc: String) {
        this.runTestPipeline("analysis/abi/G2.sol", solc, 2) { solc }
    }


    @ParameterizedTest
    @ScopedMatrix
    fun testH(solc: String) {
        this.runTestPipeline("analysis/abi/H.sol", solc, 4) { solc }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testH2(solc: String) {
        this.runTestPipeline("analysis/abi/H2.sol", solc, 1) { solc }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testI(solc: String) {
        this.runTestPipeline("analysis/abi/I.sol", solc, 1) { solc }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testK(solc: String) {
        this.runTestPipeline("analysis/abi/K.sol", solc, 1) { solc }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testHeck(solc: String) {
        this.runTestPipeline("analysis/abi/Heck.sol", solc, 1) { solc }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testDiscoveredStructBug(solc: String) {
        runBlocking {
            val contractPath = "analysis/abi/struct_bug_0.sol"
            val specPath = "analysis/abi/struct_bug_0.spec"
            val testFn = "testFn"
            val contractName = "struct_bug_0"
            runSpecTestEnsuringDirectInlining(
                contractName,
                testFn,
                setOf("f_10"),
                contractPath,
                specPath,
                solc
            ) { solc }
        }
    }

    @ParameterizedTest
    @ScopedMatrix
    fun testStructSingletonPrimitive(solc: String) = runBlocking {
        val contractPath = "analysis/abi/SingletonPrimitive.sol"
        val specPath = "analysis/abi/SingletonPrimitive.spec"
        val testFn = "f_1"
        val contractName = "SingletonPrimitive"
        runSpecTestEnsuringDirectInlining(
            contractName,
            testFn,
            setOf("f_1"),
            contractPath,
            specPath,
            solc
        ) { solc }
    }

    private suspend fun runSpecTestEnsuringDirectInlining(
        contractName: String,
        testFn: String,
        mustInline: Set<String>,
        contractPath: String,
        specPath: String,
        solc: String,
        msg: () -> String,
    ) = runSpecTestPipeline(
        contractName,
        testFn,
        contractPath,
        specPath,
        solc,
        // We just want to make sure the fn with an in-memory struct continues to be passed via direct passing
        { scene, records ->
            records.all {
                val (_, method) = it.callee.getContractAndMethod(scene)!!
                method.name !in mustInline || it.convention == Inliner.CallConventionType.DirectInlining
            }
        },
        onDirectPassingSetupFailed = { _, _ ->
            Assertions.fail {
                "$solc direct passing setup failed"
            }
        },
        msg
    )

    private suspend fun runSpecTestPipeline(
        contractName: String,
        testFn: String,
        contractPath: String,
        specPath: String,
        solc: String,
        withRecords: (scene: IScene, Collection<Inliner.CallStack.PushRecord>) -> Unit,
        onDirectPassingSetupFailed: (scene: IScene, Inliner.DirectPassingSetupFailed) -> Unit,
        msg: () -> String,
    ) {
        val contract = this.loadResourceFile(contractPath)!!
        val spec = this.loadResourceFile(specPath)!!
        DirectPassingTestPipeline.specTest(contractName, testFn, contract, spec, solc, withRecords, onDirectPassingSetupFailed, msg)
    }

    private fun runTestPipeline(path: String, solc: String, expect: Int, msg: () -> String) {
        this.runTestPipeline("Test", "test", path, solc, expect, msg)
    }

    private fun runTestPipeline(contractName: String, methodName: String, path: String, solc: String, expect: Int, msg: () -> String) {
        DirectPassingTestPipeline.checkExpectedPushRecordCount(
            this.loadScene(path, solc, address = BigInteger.TWO.pow(24)),
            contractName,
            methodName,
            expect,
            msg
        )
    }

    companion object {
        @JvmStatic
        fun certoraConfig() : List<DependentPair<*>> = listOf(
            Config.EnabledABIAnalysis setTo true,
            Config.IsAssumeUnwindCondForLoops setTo true,
        )

        fun getPushRecordsFrom(scene: Scene, contractName: String, methodName: String): Collection<Inliner.CallStack.PushRecord> {
            val contract = scene.getContracts().single { it.name == contractName }
            val testMethod = contract.getMethods().single { it.name == methodName }
            val pushes = (testMethod.code as CoreTACProgram)
                .ltacStream()
                .mapNotNull { it.maybeAnnotation(STACK_PUSH) }
                .collect(Collectors.toList())

            return pushes
        }
    }
}
