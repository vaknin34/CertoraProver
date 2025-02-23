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
import kotlinx.coroutines.flow.toList
import log.Logger
import log.LoggerTypes
import parallel.ParallelPool
import parallel.coroutines.lazy
import parallel.coroutines.RaceFinish
import smt.CEGARConfig
import smtlibutils.cmdprocessor.*
import smtlibutils.data.*
import smtlibutils.statistics.PreExecutionStatistics
import smtlibutils.statistics.ResultStatistics
import solver.ConfigStatistics
import solver.SolverConfig
import utils.*
import verifier.ConstraintChooser
import verifier.SmtConstraintsGen
import java.io.IOException
import java.nio.channels.ClosedByInterruptException
import kotlin.time.Duration.Companion.milliseconds

private val logger = Logger(LoggerTypes.SMT_CEGAR)

/**
 * A single CEGAR worker thread that alternates between LIA and NIA solving.
 */
class CEGARWorker(val state: CEGARState, val config: CEGARConfig.WorkerConfig) : AbstractWorker {

    override val name: String = "CEGAR-${config.workerID}"

    /**
     * A base worker class that is used by both the [LIAWorker] and [NIAWorker] subclasses.
     * Takes care of creating the [BaseSolver] and asserting the learned clauses.
     */
    abstract class BaseWorker(
        val state: CEGARState,
        solverConfig: SolverConfig,
        query: SmtFormulaCheckerQuery,
    ) : BaseSolver(solverConfig, query) {

        var learnedIndex = 0

        /**
         * Assert all learned clauses from [state] to the command processor.
         * Uses the query to filter the learned clauses so that we only assert compatible clauses.
         * Returns true, if new clauses have been added.
         */
        suspend fun assertLearned(): Boolean {
            cmdProcessor.process(Cmd.NoOp("start adding learned"))
            val toAdd = state.getLearned(learnedIndex)
            if (toAdd.isNotEmpty()) {
                CmdProcessor.processAssertCmds(
                    cmdProcessor,
                    filterUndefinedLiterals(toAdd, query).map {
                        state.script.assertCmd(it.exp)
                    },
                )
                learnedIndex += toAdd.size
            }
            cmdProcessor.process(Cmd.NoOp("finished adding learned"))
            return toAdd.isNotEmpty()
        }
    }

    /**
     * The linear worker that (re-) checks the linear encoding to generate candidate counterexamples that are then put
     * into the [state]'s [LIAModelQueue]. Refines the linear encoding using learned clauses (including refuted
     * counterexamples) before rechecking.
     */
    class LIAWorker private constructor(
        state: CEGARState,
        val config: CEGARConfig.WorkerConfig
    ) : BaseWorker(state, config.liaConfig, state.LIAquery) {

        companion object {
            operator suspend fun invoke(
                state: CEGARState,
                config: CEGARConfig.WorkerConfig
            ) = LIAWorker(state, config).apply {
                initialize(state.script, false /*dumpId = "cegar-${config.workerID}-lia"*/)
            }
        }

        var previousModel: Map<SmtExp, SmtExp>? = null

        /**
         * returns variables that are assigned in model1 differently than in model2 (or that are missing in model2)
         */
        private fun findModelDiff(model1: Map<SmtExp, SmtExp>, model2: Map<SmtExp, SmtExp>): List<SmtExp> {
            return model1.keys.filter { (it !in model2) || (model1[it] != model2[it]) }
        }

        private fun postprocessModel(model: Map<SmtExp, SmtExp>): Map<SmtExp, SmtExp> {
            if (previousModel != null && config.modelDiff) {
                val modelDiff = findModelDiff(model, previousModel!!)
                if (modelDiff.size <= config.modelDiffThreshold) {
                    return model.filterKeys { it !in modelDiff }
                }
            }
            return model
        }

        /**
         * Performs one check of the linear encoding. Aborts (and return a [SmtFormulaCheckerResult.Single.Void]) if the
         * linear encoding can not be refined using learned clauses. Otherwise, does the linear check and possibly
         * records new learned clauses.
         */
        suspend fun check(): SmtFormulaCheckerResultWithChecker {
            logger.info { "Worker ${config.workerID}: starting linear check" }
            val preExecStats = PreExecutionStatistics(solverConfig.getConfigStats(), listOf())
            val startTime = System.currentTimeMillis()
            // Skip if we produced a model before and we have nothing new to learn.
            if (previousModel != null && !state.hasNewLearned(learnedIndex)) {
                logger.info { "Worker ${config.workerID}: nothing to learn" }
                previousModel = null
                return SmtFormulaCheckerResult.Single.Void(msg = "skipped", null, preExecStats).withNullChecker()
            }
            assertLearned()

            // find a model of the overapproximation (if any)
            val (satResult, learnedLits) = when {
                config.learn -> queryProcessor.checkSatAndLearn()
                else -> queryProcessor.checkSat() to listOf()
            }

            val duration = (System.currentTimeMillis() - startTime).milliseconds
            state.logResult(CEGARStatsLogger.LogEntryType.LIA, solverConfig, duration, satResult, query.info.name)

            if (satResult is SatResult.UNSAT) {
                logger.info { "Worker ${config.workerID}: found UNSAT from linear" }
                val statistics = ResultStatistics(0, duration)
                return SmtFormulaCheckerResult.Single.Other(
                    satResult = satResult,
                    solverInstanceInfo = cmdProcessor.solverInstanceInfo,
                    queryInfo = query.info,
                    learnedLits = mutableListOf(), // No learned from UNSAT
                    preExecutionStatistics = preExecStats,
                    resultStats = statistics
                ).withNullChecker()
            }
            logger.debug { "Worker ${config.workerID}: adding learned" }
            state.addLearned(learnedLits)

            if (satResult is SatResult.SAT) {
                previousModel = postprocessModel(getModel())

                logger.info { "Worker ${config.workerID}: adding candidate model" }
                state.liaModelQueue.add(previousModel!!)
            } else {
                logger.info { "Worker ${config.workerID}: result is ${satResult}" }
                previousModel = null
            }
            val statistics = ResultStatistics(0, duration)
            return SmtFormulaCheckerResult.Single.Other(
                satResult = satResult,
                solverInstanceInfo = cmdProcessor.solverInstanceInfo,
                queryInfo = query.info,
                learnedLits = mutableListOf(), // TODO: Can the learned clauses be used?
                preExecutionStatistics = preExecStats,
                resultStats = statistics
            ).withNullChecker()
        }
    }

    /**
     * The nonlinear worker that verifies candidate counterexamples. Given such a candidate model, asserts the model to
     * nonlinear encoding and verifies it.
     */
    class NIAWorker private constructor(
        state: CEGARState,
        val config: CEGARConfig.WorkerConfig
    ) : BaseWorker(state, config.niaConfig, state.NIAquery) {

        companion object {
            operator suspend fun invoke(
                state: CEGARState,
                config: CEGARConfig.WorkerConfig
            ) = NIAWorker(state, config).apply {
                initialize(state.script, true /*dumpId = "cegar-${config.workerID}-lia"*/)
            }
        }

        /**
         * Takes a generalized model [model] of LIA such that NIA && [model] is UNSAT,
         * and a [spuriousNIACEX] such that [spuriousNIACEX] \subseteq [model] and NIA && [spuriousNIACEX] is UNSAT.
         * The function relaxes [model] by removing the assignments to variables that appear in [spuriousNIACEX].
         * In the overall workflow, we can again check if the relaxed model is a model of NIA.
         *
         * Note that whereas [model] is represented as a Map<SmtExp, SmtExp> (i.e., mapping variables to values),
         * [spuriousNIACEX] is represented as a list of SmtExp.Apply assignments (i.e,. <variable> = <value>).
         */
        private fun relaxModel(model: Map<SmtExp, SmtExp>, spuriousNIACEX: List<SmtExp>): Map<SmtExp, SmtExp> {
            val unsatCoreVars = spuriousNIACEX.map { literal ->
                check(literal is SmtExp.Apply && literal.args.size == 2) {
                    "Unexpected literal in an unsat core: $literal. Only variable assignments are expected here."
                }
                literal.args[0]
            }
            return model.filterNot { it.key in unsatCoreVars }
        }

        /**
         * Try to verify a candidate counterexample. If it satisfies the nonlinear encoding, we return this result.
         * If it does not and the unsat core is empty (i.e. the conflict is independent of the candidate counterexample)
         * the problem is actually unsat, and we signal this to the main worker method.
         * Otherwise, the candidate is relaxed based on the unsat core and put back into the candidate queue (unless the
         * relaxation limit is hit).
         */
        suspend fun check(model: LIAModelQueue.LIAModel): SmtFormulaCheckerResultWithChecker? {
            logger.info { "Worker ${config.workerID}: verifying candidate model" }
            state.liaModelQueue.setStatus(config.workerID, model, LIAModelQueue.SolvingStatus.STARTED)
            val startTime = getCurrentTime()
            assertLearned()

            SmtQueryProcessorContext(queryProcessor).use { context ->
                context.push()
                val modelAssert = SmtConstraintsGen(query, state.vc, state.script).getConstraintsFrom(
                    model.model,
                    ConstraintChooser.fromConstraintChooserEnum(config.constraintChooser),
                    onlyFromVc = true
                ).toList()
                val ucHelper = CoreHelper(modelAssert, SmtScript(query.symbolTable))
                CmdProcessor.processAssertCmds(
                    cmdProcessor,
                    modelAssert.asSequence().map { state.script.assertCmd(it.exp) },
                    ucHelper
                )

                val satResult: SatResult = queryProcessor.checkSat()
                val spuriousCEX = if (satResult is SatResult.UNSAT) {
                    ucHelper.parseCore(solverOutput = cmdProcessor.getUnsatCore().toList())
                    ucHelper.coreAsSmtExps
                } else {
                    null
                }
                val duration = startTime.elapsedNow()

                state.logResult(
                    CEGARStatsLogger.LogEntryType.NIA,
                    solverConfig,
                    duration,
                    satResult,
                    query.info.name,
                    cex = spuriousCEX,
                    cc = config.constraintChooser
                )

                val statistics = ResultStatistics(0, duration)
                val preExecStats = PreExecutionStatistics(solverConfig.getConfigStats(), listOf())

                if (satResult is SatResult.SAT) {
                    val niaModel = getModel()
                    logger.info { "Worker ${config.workerID}: verified model ${niaModel}" }

                    return SmtFormulaCheckerResult.Single.Other(
                        satResult = satResult,
                        solverInstanceInfo = cmdProcessor.solverInstanceInfo,
                        queryInfo = query.info,
                        getValuesResult = niaModel,
                        learnedLits = mutableListOf(), // TODO: Problem is already solved, right?
                        preExecutionStatistics = preExecStats,
                        resultStats = statistics
                    ).withNullChecker()
                } else if (satResult is SatResult.UNSAT) {
                    // proved to be unsat without using any assumptions (the LIA model)
                    logger.info { "Worker ${config.workerID}: spurious model with unsat core ${spuriousCEX!!}" }
                    state.liaModelQueue.setStatus(config.workerID, model, LIAModelQueue.SolvingStatus.REFUTED)
                    if (spuriousCEX!!.isEmpty()) {
                        logger.info { "Worker ${config.workerID}: found UNSAT from nonlinear" }
                        return SmtFormulaCheckerResult.Single.Other(
                            satResult = satResult,
                            solverInstanceInfo = cmdProcessor.solverInstanceInfo,
                            queryInfo = query.info,
                            learnedLits = mutableListOf(), // UNSAT result learned clauses are useless
                            preExecutionStatistics = preExecStats,
                            resultStats = statistics
                        ).withNullChecker()
                    } else {
                        logger.info { "Worker ${config.workerID}: blocking spurious counterexample" }
                        state.blockCEX(spuriousCEX)
                        if (model.relaxations < config.niaRelaxations) {
                            logger.info { "Worker ${config.workerID}: relaxing counterexample" }
                            state.liaModelQueue.add(relaxModel(model.model, spuriousCEX), model.relaxations + 1)
                        }
                    }
                }
                logger.info { "Worker ${config.workerID}: verification failed: ${satResult}" }
                state.liaModelQueue.setStatus(config.workerID, model, LIAModelQueue.SolvingStatus.FAILED)
                return null
            }
        }
    }

    // Initialize lazily to avoid creating the solver process when we are not actually started.
    val lia = ParallelPool.lazy { LIAWorker(state, config) }
    val nia = ParallelPool.lazy { NIAWorker(state, config) }

    /**
     * Do CEGAR-style solving, alternating linear and nonlinear checks. May stop because the linear solver found UNSAT,
     * the nonlinear solver verified a candidate counterexample or found UNSAT, or the process is stopped by the
     * [state.running] flag or terminated with an exception.
     */
    override suspend fun run(): RaceFinish<SmtFormulaCheckerResultWithChecker> {
        val errorPreExecStats = PreExecutionStatistics(ConfigStatistics("CEGAR"), listOf())
        try {
            logger.info { "Worker ${config.workerID}: starting with ${config.liaConfig} / ${config.niaConfig}" }
            while (state.running.get()) {
                var didSomething = false
                lia.await().check().let {
                    if (it.result.satResult == SatResult.UNSAT) {
                        state.running.set(false)
                        return RaceFinish.Full(it)
                    }
                    if (it.result !is SmtFormulaCheckerResult.Single.Void) {
                        didSomething = true
                    }
                }

                val model = state.liaModelQueue.getNext(config.workerID)
                if (model != null) {
                    nia.await().check(model)?.let {
                        state.running.set(false)
                        return RaceFinish.Full(it)
                    }
                    didSomething = true
                }
                if (!didSomething) {
                    delay(500)
                }
            }
            logger.info { "Worker ${config.workerID}: stopped" }
            return RaceFinish.DQF(SmtFormulaCheckerResult.Single.Void("Was stopped", null, errorPreExecStats).withNullChecker())
        } catch (e: Exception) {
            return RaceFinish.DQF(
                when (e) {
                    is ClosedByInterruptException,
                    is IOException
                    -> SmtFormulaCheckerResult.Single.Void("CEGARWorker was interrupted", null, errorPreExecStats).withNullChecker()

                    else -> {
                        logger.warn { "Worker ${config.workerID}: exception $e" }
                        SmtFormulaCheckerResult.Single.Void(
                            "CEGARWorker had an unexpected exception",
                            null,
                            errorPreExecStats
                        ).withNullChecker()
                    }
                }
            )
        }
    }

    /**
     * Close the solver processes.
     */
    @OptIn(kotlinx.coroutines.ExperimentalCoroutinesApi::class)
    override fun close() {
        lia.invokeOnCompletion { lia.getCompleted().close() }
        nia.invokeOnCompletion { nia.getCompleted().close() }
    }
}
