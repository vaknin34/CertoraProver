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

package verifier.cegar

import datastructures.stdcollections.*
import log.Logger
import log.LoggerTypes
import parallel.coroutines.RaceFinish
import smtlibutils.cmdprocessor.SmtFormulaCheckerResult
import smtlibutils.cmdprocessor.SmtFormulaCheckerResultWithChecker
import smtlibutils.cmdprocessor.withNullChecker
import smtlibutils.data.SatResult
import smtlibutils.statistics.PreExecutionStatistics
import smtlibutils.statistics.ResultStatistics
import solver.SolverConfig
import java.util.concurrent.atomic.AtomicInteger
import kotlin.time.measureTimedValue

private val logger = Logger(LoggerTypes.SMT_CEGAR)

/**
 * Single NIA executable instance that runs (only if [config.Config.CEGARPlusNIA] is set to true) in parallel
 * with the rest of the CEGAR.
 */
class ExactNIAWorker private constructor (
    val state: CEGARState,
    solverConfig: SolverConfig,
    private val workerID: Int = nextWorkerID.getAndIncrement(),
) : AbstractWorker,
    BaseSolver(solverConfig, state.NIAquery) {

    companion object {
        operator suspend fun invoke(
            state: CEGARState,
            solverConfig: SolverConfig,
            workerID: Int = nextWorkerID.getAndIncrement(),
        ) = ExactNIAWorker(state, solverConfig, workerID).apply {
            initialize(state.script, false, false)
        }

        private val nextWorkerID: AtomicInteger = AtomicInteger(1)
    }

    override val name: String = "NIA-${workerID}"

    override suspend fun run(): RaceFinish<SmtFormulaCheckerResultWithChecker> {
        val preExecStats = PreExecutionStatistics(solverConfig.getConfigStats(), listOf())
        try {
            logger.info { "NIAWorker ${workerID}: starting with $solverConfig" }
            val (satResult, duration) = measureTimedValue {
                queryProcessor.checkSat()
            }
            state.logResult(CEGARStatsLogger.LogEntryType.ExactNIA, solverConfig, duration, satResult, query.info.name)

            return if (satResult is SatResult.SAT || satResult is SatResult.UNSAT) {
                logger.info { "NIAWorker ${workerID}: found $satResult" }
                val statistics = ResultStatistics(0, duration)
                RaceFinish.Full(
                    SmtFormulaCheckerResult.Single.Other(
                        satResult = satResult,
                        solverInstanceInfo = cmdProcessor.solverInstanceInfo,
                        queryInfo = query.info,
                        getValuesResult = if (satResult is SatResult.SAT) {
                            getModel()
                        } else {
                            null
                        },
                        learnedLits = mutableListOf(), // learned clauses from UNSAT are useless
                        preExecutionStatistics = preExecStats,
                        resultStats = statistics,
                    ).withNullChecker()
                )
            } else {
                logger.info { "NIAWorker ${workerID}: was stopped" }
                val statistics = ResultStatistics(0, duration)
                RaceFinish.DQF(
                    SmtFormulaCheckerResult.Single.Other(
                        satResult = SatResult.UNKNOWN(SatResult.UnknownReason.Other()),
                        solverInstanceInfo = cmdProcessor.solverInstanceInfo,
                        learnedLits = mutableListOf(),
                        preExecutionStatistics = preExecStats,
                        resultStats = statistics
                    ).withNullChecker()
                )
            }
        } catch (e: Exception) {
            logger.info { "NIAWorker ${workerID}: was stopped with an exception" }
            return RaceFinish.DQF(
                SmtFormulaCheckerResult.Single.Void(
                    "ExactNIAWorker terminated via exception: ${e.message}", null, preExecStats
                ).withNullChecker()
            )
        }
    }
}
