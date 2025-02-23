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

package smtlibutils.cmdprocessor

import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds
import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.assertDoesNotThrow
import org.junit.jupiter.params.ParameterizedTest
import org.junit.jupiter.params.provider.ValueSource
import smtlibutils.parser.SMTParser
import solver.ArithmeticOperations
import solver.SolverChoice
import solver.SolverConfig
import utils.`impossible!`
import java.util.concurrent.Executors
import java.util.concurrent.Future
import java.util.concurrent.TimeoutException
import java.util.concurrent.TimeUnit


class InteractingCmdProcessorTest {

    private val intFormula = SMTParser.parseText(
        // something every solver can parse ..
        """
               (set-logic ALL)
               (declare-const x Int)
               (declare-const y Int)
               (declare-const z Int)
               (assert (> x y))
               (assert (= x z))
               (assert (< z y))
               (check-sat)
            """.trimIndent(),
    )

    private val bvFormula = SMTParser.parseText(
        // something every solver can parse ..
        """
               (set-logic ALL)
               (declare-const x (_ BitVec 32))
               (declare-const y (_ BitVec 32))
               (declare-const z (_ BitVec 32))
               (assert (bvugt x y))
               (assert (= x z))
               (assert (bvult z y))
               (check-sat)
            """.trimIndent(),
    )

    /**
     * Execute the given task; cancel execution when the timeout is reached.
     *
     * (This allows us to shoot down the test if the command processor gets stuck in a read operation.)
     */
    private fun <T> runBlockWithTimeout(timeout: Duration, task: () -> T): T {
        val executor = Executors.newSingleThreadExecutor()
        val future: Future<T> = executor.submit(task)
        return try {
            future.get(timeout.inWholeMilliseconds, TimeUnit.MILLISECONDS)
        } catch (e: TimeoutException) {
            future.cancel(true)
            throw e
        } catch (e: Exception) {
            throw e
        } finally {
            executor.shutdownNow()
        }
    }


    /**
     * Run all available solvers via [InteractingCmdProcessor] on a simple script.
     * One each with print-success on and off.
     */
    @ParameterizedTest
    @ValueSource(booleans = [true, false])
    fun runScript01(printSuccess: Boolean) {
        assertDoesNotThrow {
            // making this a parametrized test (over the solvers, too) might be nice, but I only found ugly solutions
            val allSolvers = SolverChoice.AllCommonAvailableSolversWithClOptions
            val options = CmdProcessor.Options.Default.copy(printSuccess = printSuccess)
            allSolvers.forEach { solverConfig ->
                val solverInfo = solverConfig.solverInfo

                val formula = when {
                    solverInfo.supportsLogicFeatures(
                        SolverConfig.LogicFeatures(
                            ArithmeticOperations.LinearOnly,
                            usesQuantifiers = false,
                            usesDatatypes = false
                        )
                    ) -> intFormula

                    solverInfo.supportsLogicFeatures(
                        SolverConfig.LogicFeatures(
                            ArithmeticOperations.BitVector,
                            usesQuantifiers = false,
                            usesDatatypes = false
                        )
                    ) -> bvFormula

                    else -> `impossible!`
                }
                runBlocking {
                    ExtraCommandsCmdProcessor.fromCommand(
                        solverInfo.name,
                        solverConfig.getCommandline(),
                        options,
                        SolverInstanceInfo.fromSolverConfig(solverConfig, options),
                    ).use { cmdProc ->
                        runBlockWithTimeout(5.seconds) {
                            runBlocking {
                                formula.cmds.forEach { cmd ->
                                    println("[${solverInfo.name}] reading: $cmd")
                                    val res = cmdProc.process(cmd)
                                    println("[${solverInfo.name}] returned: $res")
                                }
                            }
                        }
                    }
                }
            }
        }
        // if it reaches here and doesn't crash or hang, we're good ..
    }
}
