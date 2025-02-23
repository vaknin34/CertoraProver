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
import annotation.SolidityVersion
import annotations.PollutesGlobalState
import annotations.TestTags.EXPENSIVE
import config.Config
import infra.CVLFlow
import kotlinx.coroutines.runBlocking
import net.jqwik.api.*
import net.jqwik.api.lifecycle.AfterProperty
import net.jqwik.api.lifecycle.BeforeProperty
import org.junit.jupiter.api.Assertions
import report.DummyLiveStatsReporter
import scene.Scene
import solver.SolverResult
import utils.*
import utils.CollectingResult.Companion.map
import verifier.TACVerifier

@Tag(EXPENSIVE)
@Disabled //TODO CERT-7335
class DirectPassingRandomCorrectnessTests {
    @Provide
    fun simpleTest(): Arbitrary<CallTree> {
        return initialEnv()
            .flatMap {
                ArbitraryArg.callTree(it, 1, 2)
            }
    }

    @Provide
    fun singletonStaticStructTree(): Arbitrary<CallTree> {
        return initialEnv(1, 1) {
            arbitraryStruct().filter {
                it.static
            }
        }.flatMap {
            ArbitraryArg.callTree(it, 1, 3)
        }
    }

    @Provide
    fun singletonStructTree(): Arbitrary<CallTree> {
        return initialEnv(1, 1) {
            arbitraryStruct().filter {
                it.static
            }
        }.flatMap {
            ArbitraryArg.callTree(it, 1, 3)
        }
    }

    @Property(tries = 1000)
    fun testCallTreeStuff(@ForAll("simpleTest") test: CallTree) {
        checkCallSanity(test)
    }

    @Property(tries = 50)
    fun testRandomSpec(@ForAll("simpleTest") test: CallTree) =
        runBlocking { runCallTreeSpecTest(test) }

    @Property(tries = 50)
    fun testRandomSingletonStaticStruct(@ForAll("singletonStaticStructTree") test: CallTree) =
        runBlocking { runCallTreeSpecTest(test) }

    @Property(tries = 50)
    fun testRandomSingletonStruct(@ForAll("singletonStructTree") test: CallTree) =
        runBlocking { runCallTreeSpecTest(test) }

    private suspend fun runCallTreeSpecTest(test: CallTree) {
        val contractName = "test"
        val (testFn, contract, spec) = inlineEquivTestAndSpec(contractName, test)
        DirectPassingTestPipeline.specTest(
            contractName = "test",
            contract = contract,
            testFn = testFn,
            spec = spec,
            solc = SolidityVersion.V8_19.compilerName(),
            onDPSetupFailure = { _, _ ->
                Assume.that(false)
            },
            withRecords = { _, records ->
                Assume.that {
                    records.any { it.convention == Inliner.CallConventionType.DirectInlining }
                }
            },
            msg = { SolidityVersion.V8_19.compilerName() }
        )
    }

    private val configs = listOf(
        Config.EnabledABIAnalysis to true,
        Config.IsAssumeUnwindCondForLoops to true,
        Config.IsCIMode to true,
        Config.LowFootprint to true,
        Config.EnableConditionalSnippets to false,
        Config.EnableStatistics to false,
    )

    // Need this because jqwik doesn't respect jupiter stuff
    @BeforeProperty
    @PollutesGlobalState
    fun beforeProperty() {
        for ((config, setting) in configs) {
            config.set(setting)
        }
    }

    // Need this because jqwik doesn't respect jupiter stuff
    @AfterProperty
    @PollutesGlobalState
    fun afterProperty() {
        for ((config, _) in configs) {
            config.reset()
        }
    }
}
