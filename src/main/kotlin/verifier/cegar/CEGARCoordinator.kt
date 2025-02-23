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
import kotlinx.coroutines.*
import log.Logger
import log.LoggerTypes
import parallel.coroutines.*
import parallel.ParallelPool
import smt.CEGARConfig
import smtlibutils.cmdprocessor.*
import smtlibutils.data.FactorySmtScript
import smtlibutils.statistics.PreExecutionStatistics
import solver.ConfigStatistics
import utils.*
import vc.gen.LExpVC
import verifier.LExpVcChecker
import verifier.LExpVcCheckerConfig
import kotlin.time.Duration
import java.util.concurrent.atomic.AtomicInteger
import kotlin.time.Duration.Companion.ZERO

private val logger = Logger(LoggerTypes.SMT_CEGAR)

class CEGARCoordinator(val state: CEGARState) {
    private suspend fun runInternal(): SmtFormulaCheckerResultWithChecker {
        val workers: List<AbstractWorker> = state.config.workers.map {
            CEGARWorker(state, it)
        } + state.config.niaWorkers.map {
            ExactNIAWorker(state, it)
        }

        logger.info {
            val w = workers.joinToString(", ") { it.name }
            "coordinator ${coordinatorID}: starting ${state.LIAquery.info.name} with (${w})"
        }
        check(!state.running.get()) { "CEGAR coordinator ${coordinatorID} is already running" }
        state.running.set(true)

        val noStats = null
        val noPreExecStats = PreExecutionStatistics(ConfigStatistics("CEGARCoordinator"), listOf())

        var result: SmtFormulaCheckerResultWithChecker? = null
        try {
            workers.use {
                val (whoWon, ress) = ParallelPool.inherit(ParallelPool.SpawnPolicy.GLOBAL) {
                    it.rpcRace(
                        workers.map {
                            Racer(
                                it::run,
                                (state.config.timelimit + LExpVcChecker.externalSolverTimeoutPad),
                                SmtFormulaCheckerResult.Single.Cancelled(
                                    null,
                                    state.NIAquery.info,
                                    noPreExecStats
                                ).withNullChecker() // Note: Does both NIA and LIA queries
                            )
                        }
                    )
                }

                state.statsLogger.registerStats()
                // TODO: collect the complete statistics from ress.mapNotNull { it.res.resultStats }
                // TODO: for all cases

                result = if (whoWon < 0) {
                    SmtFormulaCheckerResult.Interrupted(
                        null,
                        null,
                        state.NIAquery,
                        SmtFormulaCheckerResult.Companion.InterruptReason.TIMEOUT,
                        noPreExecStats,
                        noStats
                    ).withNullChecker()
                } else {
                    when (val winner = ress[whoWon]) {
                        is RacerResult.FromJob -> {
                            winner.res
                        }

                        else -> {
                            SmtFormulaCheckerResult.Interrupted(
                                null,
                                null,
                                state.NIAquery,
                                SmtFormulaCheckerResult.Companion.InterruptReason.TIMEOUT,
                                noPreExecStats,
                                noStats
                            ).withNullChecker()
                        }
                    }
                }
            }
        } catch (e: Exception) {
            if (result == null) {
                result = SmtFormulaCheckerResult.OtherException(e, null, state.NIAquery, noPreExecStats, noStats).withNullChecker() // Todo: pass stats as part of `e`?
            }
            logger.error { "coordinator ${coordinatorID}: exception in main routine: ${e}" }
        }
        logger.info { "coordinator ${coordinatorID}: finished ${state.LIAquery.info.name} with ${result?.result?.satResult}" }
        return result!!
    }

    suspend fun run(): SmtFormulaCheckerResultWithChecker {
        return runInternal()
    }

    companion object {
        fun finalizeConfig(conf: CEGARConfig, timelimit: Duration, config: LExpVcCheckerConfig) = conf.copy(
            timelimit = if (conf.timelimit == ZERO || timelimit < conf.timelimit) { timelimit } else { conf.timelimit },
            workers = conf.workers.map {
                it.finalizeConfig(timelimit, config.configMemLimitBytes)
            },
            niaWorkers = conf.niaWorkers.map {
                it.copy(timelimit = timelimit, memlimitBytes = config.configMemLimitBytes)
            },
        )

        fun fromConfig(
            totalTimeout: Duration,
            config: LExpVcCheckerConfig,
            vc: LExpVC,
            script: FactorySmtScript,
            LIAquery: SmtFormulaCheckerQuery,
            NIAquery: SmtFormulaCheckerQuery
        ): CEGARCoordinator {
            val cconfig = finalizeConfig(config.cegarConfig, totalTimeout, config)
            val state = CEGARState(vc, script, LIAquery, NIAquery, cconfig)
            return CEGARCoordinator(state)
        }

        private val nextCoordinatorID: AtomicInteger = AtomicInteger(1)
    }

    private val coordinatorID: Int = nextCoordinatorID.getAndIncrement()
}
