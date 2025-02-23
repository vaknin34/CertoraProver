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

package verifier

import config.Config
import datastructures.stdcollections.*
import log.Logger
import log.LoggerTypes
import parallel.coroutines.RaceFinish
import smtlibutils.cmdprocessor.*
import smtlibutils.cmdprocessor.SmtFormulaCheckerResult.Companion.InterruptReason
import smtlibutils.cmdprocessor.SmtFormulaCheckerResult.Companion.Interrupted
import smtlibutils.data.FactorySmtScript
import smtlibutils.data.SatResult
import smtlibutils.data.SmtExp
import smtlibutils.statistics.*
import solver.SolverConfig
import utils.TimeSinceStart
import utils.mapSecond
import vc.gen.LExpVC
import verifier.cegar.filterUndefinedLiterals
import java.io.IOException
import java.nio.channels.ClosedByInterruptException
import java.util.concurrent.CancellationException
import kotlin.time.Duration.Companion.milliseconds

private val logger = Logger(LoggerTypes.SOLVERS)

class CEXVerifier(
    private val constraintChoosers: List<ConstraintChooser>,
    val solverConfig: SolverConfig,
    val query: SmtFormulaCheckerQuery,
    val vc: LExpVC,
    val script: FactorySmtScript
) {
    var checkerInstance: SimpleFormulaChecker? = null
    suspend fun verify(model: Map<SmtExp, SmtExp>, startTime: TimeSinceStart = TimeSinceStart()): SmtFormulaCheckerResult {
        val cg = SmtConstraintsGen(query, vc, script)
        var result: SmtFormulaCheckerResult? = null
        constraintChoosers.forEach { constraintChooser ->
            val queryToVerify = query.supplement(cg.getConstraintsFrom(model, constraintChooser))
            val solver = SimpleFormulaChecker.singleCheckerSpawnerFromSolverInfoOrNull(
                SolverInstanceInfo.fromSolverConfig(
                    solverConfig,
                    CmdProcessor.Options.fromQuery(queryToVerify, solverConfig.incremental)
                ),
                script
            )!!
            checkerInstance = solver() as SimpleFormulaChecker
            result = checkerInstance!!.check(queryToVerify, null, startTime)
            if (result!!.satResult is SatResult.SAT) {
                return result!!
            }
        }
        return LExpVcChecker.Interpretation.UnderApproximation(result!! as SmtFormulaCheckerResult.Single.Simple)
    }
}

/**
 * One query and one solver - the [exec] val is the lazy method ready to run it.
 *
 * @param winsRace says which kind of results wins the race. For example, if a solver is running on an
 *      under-approximation, then UNSAT results don't win the race.
 * @param interpretation how to translate the result of the solver.  In the example above, the UNSAT result
 *      should not appear as UNSAT, but rather as UNKNOWN.UnderApproximation
 */

class Executable(
    val raceDescription: String,
    val query: SmtFormulaCheckerQuery,
    val script: FactorySmtScript,
    val config: SolverConfig,
    val winsRace: (SatResult) -> Boolean = { result -> result !is SatResult.UNKNOWN },
    private val interpretation: LExpVcChecker.Interpretation = LExpVcChecker.Interpretation.Standard,
    private val cexVerifier: CEXVerifier? = null
) {
    val learnedLemmas = listOf<SmtExp>()

    // These two must be volatile because their update happens within exec which is run in a
    // different thread.
    @Volatile
    var checkerInstance: SimpleFormulaChecker? = null

    @Volatile
    var timeUsed: Long? = null

    @Volatile
    var execStartTime: TimeSinceStart? = null

    @Volatile
    var execThreadName: String? = null

    companion object {
        /** Wraps some exceptions that might come out setting up and running an [SmtFormulaChecker] into a nice (best
         * effort) pair of a message and an [SmtFormulaCheckerResult]. */
        fun handleNonConcurrencyRelatedExceptions(
            e: Exception,
            checkerInstance: SmtFormulaChecker?,
            query: SmtFormulaCheckerQuery,
            preExecStats: PreExecutionStatistics? = null,
            resultStats: ResultStatistics? = null
        ): Pair<String, SmtFormulaCheckerResultWithChecker> =
            when (e) {
                is IOException ->
                    // This most probably means we couldn't write to the process because it shut down for some
                    // reason.
                    "due to an IOException:\n$e" to
                        SmtFormulaCheckerResult.ProcessDied(e, checkerInstance, query, preExecStats, resultStats)

                is InteractingCmdProcessor.SMTSolverOomException ->
                    "due to running out of memory:\n$e" to
                        SmtFormulaCheckerResult.SolverOutOfMemory(e, checkerInstance, query, preExecStats, resultStats)

                is InteractingCmdProcessor.SMTSolverException ->
                    "due to an SMTSolverException:\n$e" to
                        SmtFormulaCheckerResult.SolverReportedError(e, checkerInstance, query, preExecStats, resultStats)

                is InteractingCmdProcessor.SmtSolverFailedToStartException ->
                    "due to an SmtSolverFailedToStartException:\n$e" to
                        SmtFormulaCheckerResult.SolverFailedToStart(e, checkerInstance, query, preExecStats, resultStats)

                else ->
                    "due to an unexpected Exception:\n$e" to
                        SmtFormulaCheckerResult.OtherException(e, checkerInstance, query, preExecStats, resultStats)
            }.mapSecond { r -> r.withChecker(checkerInstance) }
    }

    /**
     * runs [solver] on [query], that wraps the result in [RaceFinish.DQF] or [RaceFinish.Full] according to [winsRace]
     * This is eventually run in a different thread in a race.
     */
    suspend fun exec(critical: Boolean): RaceFinish<SmtFormulaCheckerResultWithChecker> {
        execThreadName = Thread.currentThread().name
        execStartTime = TimeSinceStart()
        val timelimit = config.timelimit ?: Config.getSolverTimeout()
        var preprocessorStatistics: List<ExecutableStatistics>? = null
        val configStats = config.getConfigStats()
        return try {
            var queryToExecute = query
            if (config.preprocessorConfig != null) {
                val preproccessorQuery = query.copy(info = query.info.copy(learn = true))
                val preprocessor = SimpleFormulaChecker.singleCheckerSpawnerFromSolverInfoOrNull(
                    SolverInstanceInfo.fromSolverConfig(
                        config.preprocessorConfig!!,
                        CmdProcessor.Options.fromQuery(preproccessorQuery, config.preprocessorConfig!!.incremental),
                        critical = critical
                    ),
                    script
                )
                if (preprocessor == null) {
                    logger.warn { "failed to create preprocessor from solverConfig ${config.preprocessorConfig!!}" }
                    RaceFinish.DQF(
                        SmtFormulaCheckerResult.CantCreateSolver(
                            query.info,
                            config.preprocessorConfig!!,
                            PreExecutionStatistics(
                                configStats,
                                null
                            )
                        )
                    )
                } else {
                    (preprocessor() as SimpleFormulaChecker).use { preprocessorInstance ->
                        val preExecStatsForPreproc = PreExecutionStatistics(config.preprocessorConfig!!.getConfigStats(), listOf())
                        val prepResult = preprocessorInstance.check(preproccessorQuery, preExecStatsForPreproc)
                        preprocessorStatistics = prepResult.collectStatistics()

                        logger.trace { "SmtFormulaChecker #${preprocessorInstance.index} finished with $prepResult." }

                        //TODO: if prepResult is SAT or UNSAT (i.e. the preprocessor solved it) then we might already finish the race here
                        if (prepResult.learnedLits?.isNotEmpty() == true) {
                            queryToExecute = query.supplement(filterUndefinedLiterals(prepResult.learnedLits
                                ?: listOf(), query))
                        }
                    }
                }
            }

            val solver = SimpleFormulaChecker.singleCheckerSpawnerFromSolverInfoOrNull(
                SolverInstanceInfo.fromSolverConfig(
                    config,
                    CmdProcessor.Options.fromQuery(queryToExecute, config.incremental),
                    critical = critical
                ),
                script
            )
            if (solver == null) {
                logger.warn { "failed to create solver from solverConfig $config" }
                RaceFinish.DQF(
                    SmtFormulaCheckerResult.CantCreateSolver(
                        queryToExecute.info,
                        config,
                        PreExecutionStatistics(configStats, preprocessorStatistics)
                    ).withNullChecker()
                )
            } else {
                checkerInstance = solver() as SimpleFormulaChecker
                val solverInstanceInfo = checkerInstance!!.solverInstanceInfo

                logger.trace {
                    val solverCommand =
                        solverInstanceInfo.takeIf { it !is SolverInstanceInfo.None }?.actualCommand?.joinToString(" ")
                            ?: "command unknown / not a simpleChecker: $checkerInstance"
                    "solver started $raceDescription ${queryToExecute.info.name} $solverCommand"
                }

                val preExecStats = PreExecutionStatistics(configStats, preprocessorStatistics)

                val result = checkerInstance!!.check(queryToExecute, preExecStats, execStartTime!!).let { res ->
                    if (res.satResult is SatResult.SAT && cexVerifier != null) {
                        cexVerifier.verify(res.getValuesResult!!, execStartTime!!).withChecker(cexVerifier.checkerInstance)
                    } else {
                        res.withChecker(checkerInstance)
                    }
                }

                logger.trace { "SmtFormulaChecker #${checkerInstance!!.index} finished with $result." }

                if (winsRace(result.result.satResult)) {
                    RaceFinish.Full(result)
                } else {
                    // In this case, it was not actually a timeout but rather the solver crashed or something
                    if (!result.result.hasTimeout && execStartTime!!.elapsedNow() > timelimit.inWholeMilliseconds.milliseconds) {
                        RaceFinish.DQF(
                            interrupted(null,
                                InterruptReason.TIMEOUT,
                                preExecStats,
                                (result.result as? SmtFormulaCheckerResult.Single.Simple)?.resultStats
                            )
                        )
                    } else {
                        RaceFinish.DQF(result)
                    }
                }
            }
        } catch (e: Exception) {
            val preExecStats = PreExecutionStatistics(configStats, preprocessorStatistics)
            val runTime = execStartTime!!.elapsedNow()

            val (exc, stats) = when (e) {
                is SimpleFormulaChecker.IOExceptionWithStats -> e.original to e.s
                else -> e to ResultStatistics(0, runTime, startTime = execStartTime, threadName = execThreadName)
            }

            val (msg, res) = when (exc) {
                is CancellationException,
                is ClosedByInterruptException,
                is InterruptedException -> when {
                    checkerInstance == null -> {
                        "another solver was faster and this one never even started" to
                            interrupted(exc, InterruptReason.SKIPPED, preExecStats, stats)
                    }

                    runTime > timelimit.inWholeMilliseconds.milliseconds -> {
                        // because of grace time added by raceSolvers, there is a small chance we actually lost the race.
                        "external timeout (or maybe race lost) reached" to
                            interrupted(exc, InterruptReason.EXTERNAL_TIMEOUT, preExecStats, stats)
                    }

                    else -> {
                        "another solver was faster to give an answer" to
                            interrupted(exc, InterruptReason.LOST_RACE, preExecStats, stats)
                    }
                }

                else -> handleNonConcurrencyRelatedExceptions(exc, checkerInstance, query, preExecStats, stats)

            }
            logger.debug { "In $raceDescription, ${query.info.name}, ${config.fullName}: $msg" }
            RaceFinish.DQF(res)
        } finally {
            timeUsed = execStartTime!!.elapsedNow().inWholeMilliseconds
        }
    }

    fun interpret(res: SmtFormulaCheckerResultWithChecker): SmtFormulaCheckerResultWithChecker {
        val r = res.result
        return if (r !is SmtFormulaCheckerResult.Single.Simple) {
            res
        } else {
            if (cexVerifier?.checkerInstance != null) {
                /** The result of the CEX verification; either TIMEOUT, SAT or underapproximation unsat **/
                LExpVcChecker.Interpretation.UnderApproximation(r).withChecker(res.checker)
            } else {
                /** The case where we did not use the prettifier **/
                interpretation(r).withChecker(res.checker)
            }
        }
    }

    fun interrupted(exception: Exception?, reason: InterruptReason, preExecStats: PreExecutionStatistics?, stats: ResultStatistics?) =
        Interrupted(exception, checkerInstance, query, reason, preExecStats, stats).withChecker(checkerInstance)
}

