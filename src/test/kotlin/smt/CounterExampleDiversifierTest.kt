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

package smt

import config.Config
import config.ConfigScope
import io.mockk.every
import io.mockk.mockk
import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Test
import report.DummyLiveStatsReporter
import scene.IScene
import solver.SolverConfig
import vc.data.TACBuilderAuxiliaries
import vc.data.TACProgramBuilder
import vc.data.TACSymbol
import vc.data.state.TACValue
import verifier.TACVerifier
import verifier.Verifier

class CounterExampleDiversifierTest : TACBuilderAuxiliaries() {
    private val mockScene = mockk<IScene>()
    init { every { mockScene.getContracts() } returns listOf() }
    private fun assertModelsEquivalent(res: Verifier.VerifierResult, models: List<Map<TACSymbol.Var, TACValue>>) {
        val cexs = res.examplesInfo.map { it.model.tacAssignments }.toMutableList()
        models.forEach { model ->
            val singleCEX = cexs.singleOrNull { cex -> model.all { cex[it.key] == it.value } }
            assert(singleCEX != null) { "${model} does not have a single cex" }
            cexs.remove(singleCEX)
        }
        assert(cexs.isEmpty()) { "the following cexs were not met: ${cexs}" }
    }

    private fun value(b: Boolean) = TACValue.valueOf(b)
    private fun value(i: Long) = TACValue.valueOf(i)

    // Set some defaults: enable multipleCEX and use only a single solver
    val baseScope = ConfigScope(Config.MultipleCEXStrategy, MultipleCEXStrategyEnum.BASIC)
        .extend(Config.Smt.OverrideSolvers, true)
        .extend(Config.Smt.BVSolvers, arrayOf())
        .extend(Config.Smt.LIASolvers, arrayOf())
        .extend(Config.Smt.NIASolvers, arrayOf(SolverConfig.z3.default))
        .extend(Config.SolverProgramChoice, arrayOf(SolverConfig.z3.default))

    @Test
    fun basicDiversityTest() {
        runBlocking {
            baseScope.extend(CounterExampleDiversifier::targetGenerator) { ctp, _ ->
                blockReachableTargets(ctp)
            }.extend(Config.MultipleCEXStrategy, MultipleCEXStrategyEnum.BASIC).use {
                val ctp = TACProgramBuilder {
                    jumpCond(x)
                    jump { assert(y) }
                    jump { assert(z) }
                }.code
                val res = TACVerifier.verify(mockScene, ctp, DummyLiveStatsReporter)
                assertModelsEquivalent(
                    res, listOf(
                        mapOf("x".boolVar to value(false), "y".boolVar to value(false)),
                        mapOf("x".boolVar to value(true), "z".boolVar to value(false)),
                    )
                )
            }
        }
    }

    @Test
    fun someMoreBlocksTest() {
        runBlocking {
            baseScope.extend(CounterExampleDiversifier::targetGenerator) { ctp, _ ->
                blockReachableTargets(ctp)
            }.extend(Config.MultipleCEXStrategy, MultipleCEXStrategyEnum.BASIC).use {
                val ctp = TACProgramBuilder {
                    jumpCond(x)
                    jump {
                        jumpCond(y)
                        jump { assert(z) }
                        jump { assert(z) }
                    }
                    jump {
                        jumpCond(y)
                        jump { assert(z) }
                        jump { assert(z) }
                    }
                }.code
                val res = TACVerifier.verify(mockScene, ctp, DummyLiveStatsReporter)
                assertModelsEquivalent(
                    res, listOf(
                        mapOf("x".boolVar to value(false), "y".boolVar to value(false), "z".boolVar to value(false)),
                        mapOf("x".boolVar to value(false), "y".boolVar to value(true), "z".boolVar to value(false)),
                        mapOf("x".boolVar to value(true), "y".boolVar to value(false), "z".boolVar to value(false)),
                        mapOf("x".boolVar to value(true), "y".boolVar to value(true), "z".boolVar to value(false)),
                    )
                )
            }
        }
    }

    @Test
    fun branchAfterViolation() {
        runBlocking {
            baseScope.extend(CounterExampleDiversifier::targetGenerator) { ctp, _ ->
                blockReachableTargets(ctp)
            }.extend(Config.MultipleCEXStrategy, MultipleCEXStrategyEnum.BASIC).use {
                val ctp = TACProgramBuilder {
                    assert(x)
                    jumpCond(y)
                    jump { assert(z) }
                    jump { assert(z) }
                }.code
                val res = TACVerifier.verify(mockScene, ctp, DummyLiveStatsReporter)
                assertModelsEquivalent(
                    res, listOf(
                        mapOf("x".boolVar to value(false)),
                        mapOf("x".boolVar to value(true), "y".boolVar to value(true), "z".boolVar to value(false)),
                        mapOf("x".boolVar to value(true), "y".boolVar to value(false), "z".boolVar to value(false)),
                    )
                )
            }
        }
    }

    @Test
    fun multiAssertTest() {
        runBlocking {
            // Without this `ConfigScope`, the program is simplified and it's not interesting.
            ConfigScope(Config.intervalsRewriter, 0).use {
                baseScope.extend(CounterExampleDiversifier::targetGenerator) { ctp, _ ->
                    userAssertionTargets(ctp)
                }.extend(Config.MultipleCEXStrategy, MultipleCEXStrategyEnum.BASIC).use {
                    val ctp = TACProgramBuilder {
                        assert(x)
                        assert(y)
                        assert(z)

                    }.code
                    val res = TACVerifier.verify(mockScene, ctp, DummyLiveStatsReporter)
                    assertModelsEquivalent(
                        res, listOf(
                            mapOf("x".boolVar to value(false)),
                            mapOf("x".boolVar to value(true), "y".boolVar to value(false)),
                            mapOf("x".boolVar to value(true), "y".boolVar to value(true), "z".boolVar to value(false)),
                        )
                    )
                }
                baseScope.extend(CounterExampleDiversifier::targetGenerator) { ctp, _ ->
                    userAssertionTargets(ctp)
                }.extend(Config.MultipleCEXStrategy, MultipleCEXStrategyEnum.BASIC).use {
                    // there should be only two CEXs: x=false and x=true,y=false
                    val ctp = TACProgramBuilder {
                        assert(x)
                        jumpCond(x)
                        jump {
                            y assign LNot(x.asSym())
                            assert(y)
                            assert(z)
                        }
                        jump {
                            z assign LOr(x.asSym(), y.asSym())
                            assert(y)
                            assert(z)
                        }
                    }.code
                    val res = TACVerifier.verify(mockScene, ctp, DummyLiveStatsReporter)
                    // TODO(gereon): fix to y after #3391
                    assertModelsEquivalent(
                        res, listOf(
                            mapOf("x".boolVar to value(false)),
                            mapOf("x".boolVar to value(true), "y!!0".boolVar to value(false)),
                        )
                    )
                }
            }
        }
    }

    @Test
    fun zeroSplitTest() {
        runBlocking {
            baseScope.extend(CounterExampleDiversifier::targetGenerator) { ctp, original ->
                splitZeroTargets(ctp, original)
            }.extend(Config.MultipleCEXStrategy, MultipleCEXStrategyEnum.BASIC).use {
                val ctp = TACProgramBuilder {
                    jumpCond(x)
                    jump { assert(x) }
                    jump {
                        z assign not(i.asSym() eq intConst(0).asSym())
                        assert(z)
                    }
                }.code
                val res = TACVerifier.verify(mockScene, ctp, DummyLiveStatsReporter)
                assertModelsEquivalent(
                    res, listOf(
                        mapOf("x".boolVar to value(false), "i".intVar to value(0)),
                    )
                )
            }
        }
    }

    @Test
    fun zeroSplitOnAmbiguousSuccessorTest() {
        runBlocking {
            System.setProperty("verbose.smt.cexdiversifier", "")
            baseScope.extend(CounterExampleDiversifier::targetGenerator) { ctp, original ->
                splitZeroTargets(ctp, original)
            }.extend(Config.MultipleCEXStrategy, MultipleCEXStrategyEnum.BASIC).use {
                val ctp = TACProgramBuilder {
                    assume(x)
                    jumpCond(x)
                    jump(1) { jump(2) }
                    jump(2) { assert(z) }
                }.code
                val res = TACVerifier.verify(mockScene, ctp, DummyLiveStatsReporter)
                res.examplesInfo.forEach {
                    println("Result: ${it.model}")
                }
                assertModelsEquivalent(
                    res, listOf(
                        mapOf("z".boolVar to value(false)),
                    )
                )
            }
        }
    }
}
