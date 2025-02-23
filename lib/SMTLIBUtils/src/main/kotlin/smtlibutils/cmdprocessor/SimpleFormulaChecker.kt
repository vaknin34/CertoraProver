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

import datastructures.stdcollections.*
import log.*
import smtlibutils.data.*
import smtlibutils.statistics.PreExecutionStatistics
import smtlibutils.statistics.ResultStatistics
import solver.*
import utils.TimeSinceStart
import java.io.IOException
import java.util.concurrent.CancellationException
import kotlin.time.Duration


open class SimpleFormulaChecker protected constructor(
    @PublishedApi internal val queryProcessor: SmtQueryProcessor,
    val solverInstanceInfo: SolverInstanceInfo
) : SmtFormulaChecker {

    /** Counter to identify each instance of this class. Here just for debugging purposes. */
    val index = queryProcessor.serial

    val name: String
        get() = solverInstanceInfo.name
    val cmdProcOptions: CmdProcessor.Options
        get() = solverInstanceInfo.options

    class IOExceptionWithStats(val original: IOException, val s: ResultStatistics): IOException()

    override suspend fun check(
        query: SmtFormulaCheckerQuery,
        preExecStats: PreExecutionStatistics?,
        startTime: TimeSinceStart,
    ): SmtFormulaCheckerResult {

        fun resultStatistics(learnedClauses: Int = 0) = ResultStatistics(
            learnedClauseOutputNum = learnedClauses,
            solverWallRuntime = startTime.elapsedNow(),
            startTime = startTime,
            threadName = Thread.currentThread().name
        )

        try {
            // make sure we're in the initial solver state
            if (queryProcessor.options.incremental) {
                queryProcessor.reset()
            }
            // send the formula to the solver
            query.assertFormulaSmtLines(queryProcessor.script).forEach {
                queryProcessor.process(it)
            }
        } catch (e: InteractingCmdProcessor.SMTSolverException) {
            // we don't know what state the solver is in now (e.g. did it ignore some assertion?) -- closing it
            queryProcessor.close()

            return SmtFormulaCheckerResult.SolverReportedError(e, this, query, preExecStats, resultStatistics())
        } catch (e: IOException) {
            throw IOExceptionWithStats(e, resultStatistics())
        }
        logger.debug { "SimpleFormulaChecker #$index ${queryProcessor.name} asserted formula, calling check-sat next." }

        val (satResult, learnedLits) =
            if(query.info.learn){
                val res = queryProcessor.checkSatAndLearn()
                logger.info { "SimpleFormulaChecker #$index ${queryProcessor.name} learned ${res.second.size}." }
                res
            }else{
                Pair(queryProcessor.checkSat(), null)
            }

        logger.info { "SimpleFormulaChecker #$index ${queryProcessor.name} terminated with result $satResult." }
        return generateSmtformulaCheckerResult(
            queryProcessor,
            query,
            satResult,
            learnedLits,
            startTime.elapsedNow(),
            preExecStats,
            resultStatistics()
        )
    }

    /** Performs a simple `(check-sat)` based on the current solver state. */
    override suspend fun checkSat(
        baseQuery: SmtFormulaCheckerQuery,
        preExecStats: PreExecutionStatistics?
    ): SmtFormulaCheckerResult.Single {
        val startTime =
            TimeSinceStart() // Note: do not use experimental time as it doesn't work with lazy sequence evaluation
        val satResult = queryProcessor.checkSat()
        val runtime = startTime.elapsedNow()
        return generateSmtformulaCheckerResult(
            queryProcessor,
            baseQuery,
            satResult,
            null,
            runtime,
            preExecStats,
            resultStats = ResultStatistics(
                0,
                runtime,
                startTime = startTime,
                threadName = Thread.currentThread().name
            ),
        )
    }

    inline fun <T> runOnQueryProcessor(op: (SmtQueryProcessor) -> T): T = op(queryProcessor)

    /**
     * Return an [SmtQueryProcessorContext] for the internal query processor. This allows to safely use `(push)` and
     * `(pop)`, making sure that all scopes are properly removed eventually.
     */
    fun getContext(): SmtQueryProcessorContext = SmtQueryProcessorContext(queryProcessor)

    override fun close() {
        logger.debug { "Closing SimpleFormulaChecker #$index ${queryProcessor.name}." }
        queryProcessor.close()
    }

    override fun toString(): String {
        return "SmplChckr(${queryProcessor.name})"
    }

    fun longToString(): String {
        return """
            SimpleFormulaChecker(${this.queryProcessor.name}):
                actual command: ${this.solverInstanceInfo.actualCommand}
            )
        """.trimIndent()
    }

    companion object {
        /**
         * don't use this function from the outside, use the solver-specific ones or a more high level one
         */
        private suspend fun singleCheckerFromSolverInstanceInfo(
            solverInstanceInfo: SolverInstanceInfo,
            script: ISmtScript,
            dumpFile: String? = null
        ): SmtFormulaChecker {
            val simple = SimpleFormulaChecker(
                SmtQueryProcessor.fromSolverInstanceInfo(solverInstanceInfo, script),
                solverInstanceInfo
            )
            val res = simple.let { checker ->
                if (dumpFile != null) {
                    SmtFormulaChecker.prependPrinter(script, solverInstanceInfo.options, checker, dumpFile)
                } else {
                    checker
                }
            }
            logger.debug {
                "Created SimpleFormulaChecker #${simple.index} from command ${
                    solverInstanceInfo.actualCommand.joinToString(" ")
                }."
            }
            return res
        }

        suspend fun plainZ3Instance(
            timeout: Duration,
            script: ISmtScript,
            options: CmdProcessor.Options? = null,
            dumpFile: String? = null
        ): SmtFormulaChecker =
            plainZ3Spawner(timeout, script, options, dumpFile)?.invoke() ?: error("failed to spawn plain z3 instance")

        /** Returns a spawner for a z3 instance in default configuration. */
        fun plainZ3Spawner(
            timeout: Duration,
            script: ISmtScript,
            options: CmdProcessor.Options? = null,
            dumpFile: String? = null
        ): (suspend () -> SmtFormulaChecker)? =
            singleCheckerSpawnerFromSolverInfoOrNull(
                SolverInstanceInfo.plainZ3(timeout, options),
                script,
                dumpFile,
            )

        /**
         * If the solver for [SolverInfo] is available, and applicable for the given options, return it, otherwise return null.
         *
         * Return a lambda that spawns a checker for the given [SolverInfo]
         */
        fun singleCheckerSpawnerFromSolverInfoOrNull(
            solverInstanceInfo: SolverInstanceInfo,
            script: ISmtScript,
            dumpFile: String? = null
        ): (suspend () -> SmtFormulaChecker)? {
            val solver = solverInstanceInfo.solverConfig.solverInfo
            val options = solverInstanceInfo.options
            return when (solver) {
                Z3SolverInfo -> { ->
                    singleZ3(
                        solverInstanceInfo,
                        script,
                        dumpFile
                    )
                }
                CVC4SolverInfo,
                CVC5SolverInfo -> { ->
                    singleCVC4or5(
                        solverInstanceInfo,
                        script,
                        dumpFile
                    )
                }
                YicesSolverInfo -> {
                    if (LogicFeature.Quantifiers !in options.logic.logicFeatures &&
                        YicesSolverInfo.isDefaultCommandAvailable
                    ) {
                        {
                            singleYices(
                                solverInstanceInfo,
                                script,
                                dumpFile
                            )
                        }
                    } else {
                        null
                    }
                }
                AltErgoSolverInfo -> {
                    if (AltErgoSolverInfo.isDefaultCommandAvailable) {
                        {
                            singleAltErgo(
                                solverInstanceInfo,
                                script,
                                dumpFile
                            )
                        }
                    } else {
                        null
                    }
                }
                VampireSolverInfo -> {
                    if (VampireSolverInfo.isDefaultCommandAvailable) {
                        {
                            singleVampire(solverInstanceInfo, script, dumpFile)
                        }
                    } else {
                        null
                    }
                }
                BitwuzlaSolverInfo -> {
                    if (BitwuzlaSolverInfo.isDefaultCommandAvailable) {
                        {
                            singleBitwuzla(solverInstanceInfo, script, dumpFile)
                        }
                    } else {
                        null
                    }
                }
                SmtInterpolSolverInfo -> {
                    if (SmtInterpolSolverInfo.isDefaultCommandAvailable) {
                        {
                            singleSmtInterpol(solverInstanceInfo, script, dumpFile)
                        }
                    } else {
                        null
                    }
                }
                else -> error("unrecognized solver ($solver), did we add a new solver but not register it everywhere?")
            }
        }

        /** Return a checker with Bitwuzla.  */
        private suspend fun singleBitwuzla(
            solverInstanceInfo: SolverInstanceInfo,
            script: ISmtScript,
            dumpFile: String? = null
        ): SmtFormulaChecker {
            if (solverInstanceInfo.solverConfig.solverInfo != BitwuzlaSolverInfo) {
                throw IllegalArgumentException("this may not be called for another solver than Bitwuzla")
            }
            return singleCheckerFromSolverInstanceInfo(
                (solverInstanceInfo as SolverInstanceInfo.Standard).copy(
                    options = solverInstanceInfo.options.copy1(
                        queryDifficulties = false, // bitwuzla doesn't support (get-difficulty) so far
                        queryUnknownReason = false, // bitwuzla does not seem to support this
                    )
                ),
                script,
                dumpFile
            )
        }

        private suspend fun singleSmtInterpol(
            solverInstanceInfo: SolverInstanceInfo,
            script: ISmtScript,
            dumpFile: String? = null
        ): SmtFormulaChecker {
            if (solverInstanceInfo.solverConfig.solverInfo != SmtInterpolSolverInfo) {
                throw IllegalArgumentException("this may not be called for another solver than Bitwuzla")
            }
            return singleCheckerFromSolverInstanceInfo(
                (solverInstanceInfo as SolverInstanceInfo.Standard).copy(
                    options = solverInstanceInfo.options.copy1(
                        queryDifficulties = false, // smtinterpol doesn't support (get-difficulty) so far
                    )
                ),
                script,
                dumpFile
            )
        }

        /** Return a checker with CVC5, or, for legacy reasons, CVC4.  */
        private suspend fun singleCVC4or5(
            solverInstanceInfo: SolverInstanceInfo,
            script: ISmtScript,
            dumpFile: String? = null
        ): SmtFormulaChecker {
            /* needs no special treatment so far */
            if (solverInstanceInfo.solverConfig.solverInfo != CVC5SolverInfo && solverInstanceInfo.solverConfig.solverInfo != CVC4SolverInfo) {
                throw IllegalArgumentException("this may not be called for another solver than CVC5 (or CVC4)")
            }
            val sii = solverInstanceInfo.copy1(
                options = solverInstanceInfo.options.copy1(
                    queryDifficulties =
                    if (solverInstanceInfo.solverConfig.solverInfo == CVC5SolverInfo) {
                        solverInstanceInfo.options.queryDifficulties
                    } else {
                        false
                    }// cvc4 doesn't support (get-difficulty)

                )
            )
            return singleCheckerFromSolverInstanceInfo(sii, script, dumpFile)
        }

        private suspend fun singleZ3(
            solverInstanceInfo: SolverInstanceInfo,
            script: ISmtScript,
            dumpFile: String? = null
        ): SmtFormulaChecker {
            if (solverInstanceInfo.solverConfig.solverInfo != Z3SolverInfo) {
                throw IllegalArgumentException("this may not be called for another solver than Z3")
            }

            /* z3 doesn't admit it supports some data types logics, like QF_UFDTLIA. If we just use ALL, it should work
             * nonetheless (and avoid the inconsequential error message).  */
            val finalLogicForZ3 =
                if (LogicFeature.DataTypes in solverInstanceInfo.options.logic.logicFeatures) {
                    Logic.ALL
                } else {
                    solverInstanceInfo.options.logic
                }
            val finalSolverInstanceInfo =
                when (solverInstanceInfo) {
                    SolverInstanceInfo.None -> solverInstanceInfo
                    is SolverInstanceInfo.Standard ->
                        solverInstanceInfo.copy(
                            options = solverInstanceInfo.options.copy1(
                                logic = finalLogicForZ3,
                                queryDifficulties = false, // z3 doesn't support (get-difficulty) so far
                            )
                        )
                }

            return singleCheckerFromSolverInstanceInfo(finalSolverInstanceInfo, script, dumpFile)
        }

        private suspend fun singleYices(
            solverInstanceInfo: SolverInstanceInfo,
            script: ISmtScript,
            dumpFile: String? = null
        ): SmtFormulaChecker {
            if (solverInstanceInfo.solverConfig.solverInfo != YicesSolverInfo) {
                throw IllegalArgumentException("this may not be called for another solver than Yices")
            }
            if (LogicFeature.Quantifiers in solverInstanceInfo.options.logic.logicFeatures) {
                throw IllegalArgumentException("yices can't handle quantified logics")
            }
            val sii = solverInstanceInfo.copy1(
                options = solverInstanceInfo.options.copy1(
                    queryDifficulties = false // yices doesn't support (get-difficulty) so far
                )
            )
            return singleCheckerFromSolverInstanceInfo(sii, script, dumpFile)
        }

        private suspend fun singleAltErgo(
            solverInstanceInfo: SolverInstanceInfo,
            script: ISmtScript,
            dumpFile: String? = null
        ): SmtFormulaChecker {
            if (solverInstanceInfo.solverConfig.solverInfo != AltErgoSolverInfo) {
                throw IllegalArgumentException("this may not be called for another solver than Alt-Ergo")
            }
            if (solverInstanceInfo.options.incremental) {
                throw IllegalArgumentException(
                    "Alt-Ergo doesn't support incremental model " +
                        "(or at least it's behaviour should be investigated ...)."
                )
            }
            return singleCheckerFromSolverInstanceInfo(
                solverInstanceInfo.copy1(
                    options = solverInstanceInfo.options.copy1(
                        produceUnsatCores = false,
                        produceModels = false,
                        printSuccess = false,
                        oneOffSolver = true,
                        queryDifficulties = false, // alt-ergo doesn't support (get-difficulty) so far
                    )
                ),
                script,
                dumpFile
            )
        }

        private suspend fun singleVampire(
            solverInstanceInfo: SolverInstanceInfo,
            script: ISmtScript,
            dumpFile: String? = null
        ): SmtFormulaChecker {
            if (solverInstanceInfo.solverConfig.solverInfo != VampireSolverInfo)
                throw IllegalArgumentException("this may not be called for another solver than Vampire")
            if (solverInstanceInfo.options.incremental)
                throw IllegalArgumentException("Vampire doesn't support incremental mode.")
            /** Vampire is a bit picky with its logics ... */
            fun findALogicForVampire(logic: Logic): Logic = Logic.fromFeatures(
                logic.logicFeatures +
                    LogicFeature.Quantifiers +
                    LogicFeature.UninterpretedFunctions +
                    LogicFeature.Arrays
            )

            return singleCheckerFromSolverInstanceInfo(
                solverInstanceInfo.copy1(
                    options = solverInstanceInfo.options.copy1(
                        logic = findALogicForVampire(solverInstanceInfo.options.logic),
                        produceUnsatCores = false,
                        produceModels = false,
                        printSuccess = false,
                        oneOffSolver = true,
                        queryUnknownReason = false,
                        queryDifficulties = false, // vampire doesn't support (get-difficulty) so far
                    )
                ),
                script,
                dumpFile
            )
        }
    }

    class ExceptionWithStats(e: Exception, val stats: ResultStatistics): Exception(e)

    /**
     * Finishes up the solver interaction with queries depending on the result.
     * If result was SAT, obtains values from the model.
     * If result was UNSAT, obtains an unsat core if the option is set.
     *
     * If result was UNKNOWN, obtains unknown-reason or difficulties, depending on options.
     *
     * Note that after doing the queries, this resets [qp], thus the underlying z3/cvc4 instance, including the
     * script (with it's symbol table).
     *
     * Contains [simpleFormulaChecker], the checker that produced this result.
     */
    private suspend fun generateSmtformulaCheckerResult(
        qp: SmtQueryProcessor,
        query: SmtFormulaCheckerQuery,
        satResult: SatResult,
        learnedLits: List<SmtExp>? = null,
        checkSatRuntime: Duration,
        preExecStats: PreExecutionStatistics?,
        resultStats: ResultStatistics,
    ): SmtFormulaCheckerResult.Single.Simple {
        val res = when (satResult) {
            SatResult.UNSAT -> {
                if (query.info.getUnsatCore) {
                    check(query.coreHelper != null)
                    { "Illegal query: has `getUnsatCore` set to true, but no unsatCoreHelper ($query)." }
                    qp.getUnsatCore(query.coreHelper)
                    SmtFormulaCheckerResult.Single.Simple(
                        solverInstanceInfo,
                        satResult,
                        null,
                        query.coreHelper,
                        query,
                        learnedLits,
                        checkSatRuntime,
                        preExecutionStatistics = preExecStats,
                        resultStats = resultStats
                    )
                } else {
                    SmtFormulaCheckerResult.Single.Simple(
                        solverInstanceInfo,
                        satResult,
                        null,
                        null,
                        query,
                        learnedLits,
                        checkSatRuntime,
                        preExecutionStatistics = preExecStats,
                        resultStats = resultStats
                    )
                }
            }
            is SatResult.UNKNOWN -> {
                val satResultWithReason =
                    if (qp.options.queryUnknownReason && !qp.options.oneOffSolver) {
                        try {
                            val unknownReason = qp.getUnknownReason()
                            logger.debug { "(${qp.name}:) got $unknownReason as reason-unknown" }
                            logger.debug { "satResult was $satResult" }
                            satResult.withReason(SatResult.UnknownReason.parseFromGetInfo(unknownReason))

                        } catch (e: Exception) {
                            when (e) {
                                is IOException,
                                is InteractingCmdProcessor.SMTSolverException -> {
                                    logger.debug { "(${qp.name}:) failed to get reason-unknown, solver gave error" }
                                    logger.debug { "satResult was $satResult" }
                                    SatResult.UNKNOWN.solverReportedError(e)
                                }
                                else -> throw ExceptionWithStats(e, resultStats)
                            }
                        }
                    } else {
                        logger.debug {
                            "Cannot get unknown reason since ${qp.name} is a \"one-off\" solver or " +
                                "the option is switched off in CmdProcessor.Options (${qp.options})."
                        }
                        satResult
                    }
                val satResultWithDifficulties: SatResult =
                // this check looks redundant, but we need the CmdProcessor options, because they can be solver
                //  -specific, as opposed to the query. E.g. some query Q might be posed to z3 and cvc5, but
                    //  only cvc5 supports the (get-difficulty) command.
                    if (query.info.getDifficulties &&
                        qp.options.queryDifficulties &&
                        !qp.options.oneOffSolver &&
                        !qp.options.noAnswers
                    ) {
                        try {
                            val difficultiesLines = qp.getDifficulties()
                            logger.debug { "(${qp.name}:) got $difficultiesLines as difficulties" }
                            logger.debug { "satResult was $satResultWithReason" }
                            (satResultWithReason as
                                SatResult.UNKNOWN).withDifficulties(Difficulties.parse(difficultiesLines))
                        } catch (e: Exception) {
                            when (e) {
                                is IOException,
                                is InteractingCmdProcessor.SMTSolverException -> {
                                    logger.debug { "(${qp.name}:) failed to get difficulties, solver gave error" }
                                    logger.debug { "satResult was $satResultWithReason" }
                                    satResultWithReason
                                }
                                else -> throw ExceptionWithStats(e, resultStats)
                            }
                        }
                    } else {
                        logger.debug {
                            "Cannot get difficulties since ${qp.name} is a \"one-off\" solver or " +
                                "the option is switched off in CmdProcessor.Options (${qp.options})." +
                                "(The latter might be because ${qp.name} does not support the " +
                                "(get-difficulty command)."
                        }
                        satResultWithReason
                    }

                logger.debug { "satResult that goes into the SmtFormulaCheckerResult: $satResultWithDifficulties" }

                SmtFormulaCheckerResult.Single.Simple(
                    solverInstanceInfo,
                    satResultWithDifficulties,
                    null,
                    query.coreHelper,
                    query,
                    learnedLits,
                    checkSatRuntime,
                    preExecutionStatistics = preExecStats,
                    resultStats = resultStats
                )
            }
            is SatResult.SAT -> {
                if (!query.termsOfInterest.isEmpty() && qp.options.oneOffSolver) {
                    logger.warn { "${qp.name} is a \"one-off\" solver -- cannot a model (or single values) from it." }
                    SmtFormulaCheckerResult.Single.Simple(
                        solverInstanceInfo,
                        satResult,
                        null,
                        null,
                        query,
                        learnedLits,
                        checkSatRuntime,
                        preExecutionStatistics = preExecStats,
                        resultStats = resultStats
                    )
                } else if (!query.termsOfInterest.isEmpty() && !qp.options.oneOffSolver) {
                    val values = try {
                        qp.getValue(query.termsOfInterest.toList(), query.symbolTable)
                    } catch (e: CancellationException) {
                        // We are somewhat frequently cancelled here, so we forward the CancellationException.
                        throw e
                    } catch (e: IllegalStateException) {
                        logger.error(e, "failed to parse model for smt query \"${query.info.name}\"")
                        throw e
                    }
                    SmtFormulaCheckerResult.Single.Simple(
                        solverInstanceInfo,
                        satResult,
                        values,
                        null,
                        query,
                        learnedLits,
                        checkSatRuntime,
                        preExecutionStatistics = preExecStats,
                        resultStats = resultStats
                    )
                } else {
                    SmtFormulaCheckerResult.Single.Simple(
                        solverInstanceInfo,
                        satResult,
                        null,
                        null,
                        query,
                        learnedLits,
                        checkSatRuntime,
                        preExecutionStatistics = preExecStats,
                        resultStats = resultStats
                    )
                }
            }
        }
        return res
    }
}

class PrintingFormulaChecker private constructor(
    queryProcessor: SmtQueryProcessor,
    solverInstanceInfo: SolverInstanceInfo
) : SimpleFormulaChecker(queryProcessor, solverInstanceInfo) {
    companion object {
        suspend fun printer(script: ISmtScript, dumpFile: String, options: CmdProcessor.Options): PrintingFormulaChecker =
            PrintingFormulaChecker(
                SmtQueryProcessor(
                    script,
                    "printer(file:${dumpFile})",
                    ExtraCommandsCmdProcessor.fromCmdProcessor(PrintingCmdProcessor(dumpFile, options.copy1(noAnswers = true)))
                ),
                SolverInstanceInfo.None
            )
    }
}

private val logger = Logger(SMTLIBUtilsLoggerTypes.SMT_SIMPLEFORMULACHECKER)
