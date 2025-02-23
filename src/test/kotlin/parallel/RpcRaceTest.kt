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

package parallel

import kotlinx.coroutines.TimeoutCancellationException
import kotlinx.coroutines.flow.collect
import kotlinx.coroutines.*
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import parallel.coroutines.RaceFinish
import parallel.coroutines.Racer
import parallel.coroutines.RacerResult
import parallel.coroutines.rpcRace
import smtlibutils.cmdprocessor.*
import smtlibutils.parser.SMTParser
import solver.SolverConfig
import java.nio.channels.ClosedByInterruptException
import java.util.concurrent.TimeoutException
import kotlin.time.Duration.Companion.milliseconds
import kotlin.time.Duration.Companion.seconds
import kotlin.time.measureTime

/**
 * This would usually belong to `lib/GeneralUtils/src/test/...`, but we need utilities for this test that are not
 * available in that package.
 * Here, we test various ways the coroutines generally and `rpcRace` in particular might be used, and whether
 * timeouts are honored.
 */
class RpcRaceTest {

    val solvers = listOf(SolverConfig.z3.def, SolverConfig.cvc5.def)
    val options = CmdProcessor.Options.Default
    // Nothing special about this formula. Just make sure it's sufficiently hard to solve...
    val formula = SMTParser.parseText(
        """
            (set-logic ALL)
            (declare-const a (_ BitVec 256))
            (declare-const b (_ BitVec 256))
            (declare-const c (_ BitVec 256))
            (declare-const d (_ BitVec 256))
            (assert (= a (bvmul b c)))
            (assert (= a (bvadd c b)))
            (assert (= d (bvudiv b a)))
            (assert (bvult a b))
            (assert (bvult d a))
            (assert (bvult (_ bv1234567890 256) a))
            (assert (bvult (_ bv1234567890 256) b))
            (assert (bvult (_ bv1234567890 256) c))
            (assert (bvult (_ bv1234567890 256) d))
            (check-sat)
        """.trimIndent()
    )


    @Test
    /**
     * This should be more or less the simplest way to run a solver with a timeout via coroutines.
     * Check that a [TimeoutException] is triggered and the timeout is enforced reasonably timely.
     */
    fun reconstructWithTimeout() {
        var didTimeout = false
        val solverConfig = solvers.first()
        val timing = measureTime {
            try {
                runBlocking {
                    ParallelPool.inherit(ParallelPool.SpawnPolicy.GLOBAL) {
                        withTimeout(1.seconds) {
                            ExtraCommandsCmdProcessor.fromCommand(
                                solverConfig.solverInfo.name,
                                solverConfig.getCommandline(),
                                options,
                                SolverInstanceInfo.fromSolverConfig(solverConfig, options),
                            ).use { cmdProc ->
                                formula.cmds.forEach { cmd ->
                                    cmdProc.process(cmd)
                                }
                            }
                        }
                    }
                }
            } catch (e: ClosedByInterruptException) {
                didTimeout = true
            } catch (e: TimeoutCancellationException) {
                didTimeout = true
            }
        }
        assertTrue(didTimeout)
        assertTrue(timing >= 1.seconds)
        assertTrue(timing <= 1500.milliseconds)
    }

    @Test
    /**
     * Here we use [rpcRace] with explicit [Racer]s.
     * Check that a [TimeoutException] is triggered and the timeout is enforced reasonably timely.
     */
    fun rpcRaceWithRacersAndTimeout() {
        val timing = measureTime {
            val results =
                runBlocking {
                    ParallelPool.inherit(ParallelPool.SpawnPolicy.GLOBAL) {
                        it.rpcRace(
                            solvers.map { solverConfig ->
                                Racer(
                                    {
                                        ExtraCommandsCmdProcessor.fromCommand(
                                            solverConfig.solverInfo.name,
                                            solverConfig.getCommandline(),
                                            options,
                                            SolverInstanceInfo.fromSolverConfig(solverConfig, options),
                                        ).use { cmdProc ->
                                            formula.cmds.forEach { cmd ->
                                                cmdProc.process(cmd)
                                            }
                                        }
                                        RaceFinish.Full(15)
                                    },
                                    1.seconds,
                                    SmtFormulaCheckerResult.Single.Cancelled().withNullChecker()
                                )
                            }
                        )
                    }
                }
            assertTrue(results.second.all { it is RacerResult.Timeout })
        }
        assertTrue(timing >= 1.seconds)
        assertTrue(timing <= 1500.milliseconds)
    }


    @Test
    /**
     * Here we use [rpcRace] with lambdas.
     * Check that a [TimeoutException] is triggered and the timeout is enforced reasonably timely.
     */
    fun rpcRaceWithTimeout() {
        val timing = measureTime {
            val results = runBlocking {
                with(ParallelPool()) {
                    solvers.rpcRace(1.seconds) { solverConfig ->
                        ExtraCommandsCmdProcessor.fromCommand(
                            solverConfig.solverInfo.name,
                            solverConfig.getCommandline(),
                            options,
                            SolverInstanceInfo.fromSolverConfig(solverConfig, options),
                        ).use { cmdProc ->
                            formula.cmds.forEach { cmd ->
                                cmdProc.process(cmd)
                            }
                        }
                        RaceFinish.Full(15)
                    }
                }
            }
            assertTrue(results.second.all { it is RacerResult.Timeout })
        }
        assertTrue(timing >= 1.seconds)
        assertTrue(timing <= 1500.milliseconds)
    }
}
