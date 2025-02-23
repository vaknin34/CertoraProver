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
import smtlibutils.data.SatResult
import smtlibutils.data.SmtExp
import smtlibutils.statistics.ExecutableStatistics
import smtlibutils.statistics.PreExecutionStatistics
import smtlibutils.statistics.ResultStatistics
import solver.SolverConfig
import utils.*
import kotlin.time.Duration

/**
 *
 * `TACVerifier` represents the result of a VC check as the type `SmtFormulaCheckerResult`.  The type consists of the
 * following hierarchy of classes:
 * ```mermaid
 * classDiagram
 * SmtFormulaCheckerResult <|-- Single
 * SmtFormulaCheckerResult <|-- Agg
 * Agg <|-- SequentialResult
 * Agg <|-- ParallelResult
 * Agg <|-- LExpVcCheckerResult
 * Single <|-- Simple
 * Single <|-- Void
 * Single <|-- Other
 * Single <|-- Cancelled
 * ```
 * where `SmtFormulaCheckerResult`, `Agg` and `Single` are abstract.
 * The classes contain information including the query, the sat result, and the statistics.  Each class under `Agg`
 * contains potentially more `SmtFormulaCheckerResult`s as subresults, and information obtained directly from an SMT
 * solver (*) is available in classes under `Single`.
 *
 * An instance of an `SmtFormulaCheckerResult` can be interpreted as a *result tree* of instances where leaf nodes are
 * of type `Single` and internal nodes (including root, if it has children) are of type `Agg`, and the edges are
 * directed from the root to the leaves.  A *rooted path* in this tree is a path that traverses along the edges of the
 * tree from the root to a leaf.
 *
 * (*) this is not currently true for CEGAR results.  They are `Single` results even if they consist of several runs
 * of SMT solvers.
 *
 * ## Logging races
 * A race consists of a set of solver runs aiming at solving functionally the same problem.  Due to the structure of
 * `TACVerifier` implementation it is difficult to trace statistics of a race.
 *
 * As a solution to the race logging problem, a node in the result tree can be labeled with a `RaceInfo` that collects
 * statistics relevant to the race as well as an `id` that identifies uniquely the race within an `LExpVcChecker`
 * instance.  For correct race logging, `LExpVcChecker` should guarantee that every result of type `Single` corresponds
 * to exactly one race.  In the tree structure this is enforced so that every rooted path contains exactly one node
 * labeled with a non-null `RaceInfo`.  Such nodes are called *race nodes*.  Race nodes are not necessarily unique to
 * a node: it is possible that several race nodes are labeled with the same `RaceInfo`.
 */

class RaceInfo(
    val id: Int,
    val raceDescription: String,
    val runTime: Duration,
    val timeout: Duration,
    val startTime: TimeSinceStart,
)


sealed class SmtFormulaCheckerResult : java.io.Serializable {
    abstract val solverInstanceInfo: SolverInstanceInfo?
    abstract val satResult: SatResult
    /** Result of the `(get-value <terms of interest>)` call, which we do in the SAT case.
     * (i.e. the model that the solver found, restricted to the terms that we're querying)  */
    abstract val getValuesResult: Map<SmtExp, SmtExp>?
    abstract val unsatCore: CoreHelper?
    abstract val learnedLits: List<SmtExp>?

    abstract val subResults: List<SmtFormulaCheckerResult>
    abstract val subResultsFlattened: List<Single>
    abstract val hasTimeout: Boolean
    abstract val hasOom: Boolean

    abstract val representativeResult: Single

    var raceInfo: RaceInfo? = null
    fun registerToRace(id: Int, raceDescription: String, runTime: Duration, timeout: Duration, startTime: TimeSinceStart) {
        raceInfo = RaceInfo(id, raceDescription, runTime, timeout, startTime)
    }

    abstract fun collectStatistics(): List<ExecutableStatistics>
    fun hasTimeoutOrOom(): Boolean {
        return hasTimeout || hasOom
    }

    sealed class Single : SmtFormulaCheckerResult() {
        override val subResults: List<SmtFormulaCheckerResult>
            get() = listOf(this)

        override val subResultsFlattened: List<Single>
            get() = listOf(this)

        override val representativeResult: Single
            get() = this

        abstract val queryInfo: SmtFormulaCheckerQueryInfo?
        abstract val query: SmtFormulaCheckerQuery?
        abstract val resultStats: ResultStatistics?
        abstract val preExecutionStatistics: PreExecutionStatistics?

        /**
         * @param unsatCore the unsat core is given as an [CoreHelper] (which has a field called unsatCore)
         * @param query the query that this result is an answer to
         * @param checkSatRuntime run time from adding the smt command to after returning from check-sat
         *     (might be null e.g. in case of an error, so check-sat never returned)
         */
        data class Simple(
            override val solverInstanceInfo: SolverInstanceInfo?,
            override val satResult: SatResult,
            override val getValuesResult: Map<SmtExp, SmtExp>?,
            override val unsatCore: CoreHelper?,
            override val query: SmtFormulaCheckerQuery,
            override val learnedLits: List<SmtExp>?,
            val checkSatRuntime: Duration?,
            val postProcessModelResult: PostProcessModel.PostProcessModelResult? = null,
            override val preExecutionStatistics: PreExecutionStatistics?,
            override val resultStats: ResultStatistics?,
            override val queryInfo: SmtFormulaCheckerQueryInfo = query.info,
        ) : Single() {

            override fun collectStatistics(): List<ExecutableStatistics> =
                listOf(ExecutableStatistics(queryInfo.statistics, preExecutionStatistics, resultStats, satResult))

            override val hasTimeout: Boolean
                get() = satResult is SatResult.UNKNOWN && satResult.reason.isTimeout

            override val hasOom: Boolean
                get() = satResult is SatResult.UNKNOWN && satResult.reason.isOom

            override fun toString(): String = "SmtFormulaCheckerResult.Simple($satResult)"

            override fun longToString(): String {
                return "SmtFormulaCheckerResultSingle(\n" +
                        "\tsatResult=$satResult,\n" +
                        "\tgetValuesResult=$getValuesResult,\n" +
                        "\tunsatCore=$unsatCore,\n" +
                        "\tquery=$query)"
            }

        }

        /** Represents failure to run solvers at all or something like that. */
        data class Void(
            val msg: String,
            override val queryInfo: SmtFormulaCheckerQueryInfo?,
            override val preExecutionStatistics: PreExecutionStatistics?,
            override val hasTimeout: Boolean = false,
        ) : Single() {
            override val query: SmtFormulaCheckerQuery? = null
            override val solverInstanceInfo: SolverInstanceInfo? = null
            override val satResult: SatResult
                get() = SatResult.UNKNOWN(SatResult.UnknownReason.NoSolvers)
            override val getValuesResult: Map<SmtExp, SmtExp>?
                get() = null
            override val learnedLits: List<SmtExp>?
                get() = null
            override val resultStats: ResultStatistics? = null


            override fun collectStatistics(): List<ExecutableStatistics> =
                listOf(ExecutableStatistics(queryInfo?.statistics, preExecutionStatistics, null, satResult))

            override val unsatCore: CoreHelper?
                get() = null
            override val hasOom: Boolean
                get() = false
        }

        /** E.g. for PathEnum results where we don't have all the infra set up yet. */
        data class Other(
            override val satResult: SatResult,
            override val solverInstanceInfo: SolverInstanceInfo? = null,
            override val queryInfo: SmtFormulaCheckerQueryInfo? = null,
            override val getValuesResult: Map<SmtExp, SmtExp>? = null,
            override val learnedLits: List<SmtExp>? = null,
            override val preExecutionStatistics: PreExecutionStatistics? = null,
            override val resultStats: ResultStatistics? = null,
        ) : Single() {
            override val query: SmtFormulaCheckerQuery? = null
            override val unsatCore: CoreHelper?
                get() = null
            override val hasTimeout: Boolean
                get() = satResult is SatResult.UNKNOWN && satResult.reason.isTimeout

            override val hasOom: Boolean
                get() = satResult is SatResult.UNKNOWN && satResult.reason.isOom

            override fun collectStatistics(): List<ExecutableStatistics> =
                listOf(ExecutableStatistics(queryInfo?.statistics, preExecutionStatistics, resultStats, satResult))
        }

        data class Cancelled(
            override val solverInstanceInfo: SolverInstanceInfo? = null,
            override val queryInfo: SmtFormulaCheckerQueryInfo? = null,
            override val preExecutionStatistics: PreExecutionStatistics? = null,
        ) : Single() {
            override val query: SmtFormulaCheckerQuery? = null
            override val satResult: SatResult
                get() = SatResult.UNKNOWN(SatResult.UnknownReason.Interrupted)
            override val getValuesResult: Map<SmtExp, SmtExp>?
                get() = null
            override val learnedLits: List<SmtExp>?
                get() = null
            override val unsatCore: CoreHelper?
                get() = null
            override val hasTimeout: Boolean
                get() = false
            override val hasOom: Boolean
                get() = false

            override val resultStats = null

            override fun collectStatistics(): List<ExecutableStatistics> =
                listOf(ExecutableStatistics(queryInfo?.statistics, preExecutionStatistics, resultStats, satResult))
        }


    }

    sealed class Agg : SmtFormulaCheckerResult() {

        override val solverInstanceInfo: SolverInstanceInfo?
            get() = representativeResult.solverInstanceInfo

        override val satResult: SatResult
            get() = representativeResult.satResult
        override val getValuesResult: Map<SmtExp, SmtExp>?
            get() = representativeResult.getValuesResult
        override val learnedLits: List<SmtExp>?
            get() = representativeResult.learnedLits
        override val unsatCore: CoreHelper?
            get() = representativeResult.unsatCore

        abstract val unknownResults: Collection<SmtFormulaCheckerResult>

        override val subResultsFlattened: List<Single>
            get() = subResults.flatMap { it.subResultsFlattened }

        val unknownSimpleResultsFlat: Collection<Single.Simple>
                by lazy {
                    unknownResults.flatMap {
                        when (it) {
                            is Single.Other,
                            is Single.Cancelled,
                            is Single.Void -> listOf()
                            is Single.Simple -> listOf(it)
                            is Agg -> it.unknownSimpleResultsFlat
                        }
                    }
                }

        val sampleTimeoutResult: Single.Simple?
            get() = unknownSimpleResultsFlat.find { (it.satResult as SatResult.UNKNOWN).reason.isTimeout }

        val sampleOomResult: Single.Simple?
            get() = unknownSimpleResultsFlat.find { (it.satResult as SatResult.UNKNOWN).reason.isOom }

        override val hasTimeout: Boolean
            get() = sampleTimeoutResult != null

        override val hasOom: Boolean
            get() = sampleOomResult != null

        data class SequentialResult(
            val sequentialFormulaChecker: SequentialFormulaChecker,
            val successfulResult: SmtFormulaCheckerResult?,
            override val unknownResults: Collection<SmtFormulaCheckerResult>,
            val queryInfo: SmtFormulaCheckerQueryInfo,
        ) : Agg() {
            override fun collectStatistics(): List<ExecutableStatistics> =
                (successfulResult?.collectStatistics() ?: listOf()) +
                    unknownResults.map { it.collectStatistics() }.flatten()

            override val subResults: List<SmtFormulaCheckerResult>
                get() = listOfNotNull(successfulResult) + unknownResults

            override val representativeResult =
                successfulResult?.let {
                    when (it) {
                        is Agg -> it.representativeResult
                        is Single -> it
                    }
                }
                    ?: sampleTimeoutResult
                    ?: sampleOomResult
                    ?: unknownResults.lastOrNull()?.let {
                        when (it) {
                            is Agg -> it.representativeResult
                            is Single -> it
                        }
                    }
                    ?: Single.Void("no result available -- error?", queryInfo, null)
        }

        data class LExpVcCheckerResult(
            val finalRes: Single?,
            val otherResults: List<Single> // unknowns and other successful solvers
        ) : Agg() {

            override val unknownResults =
                otherResults.filter { it.satResult is SatResult.UNKNOWN }

            override val subResults: List<SmtFormulaCheckerResult>
                get() = listOfNotNull(finalRes) + otherResults

            override val representativeResult =
                finalRes
                    ?: sampleTimeoutResult
                    ?: sampleOomResult
                    ?: unknownResults.lastOrNull()
                    ?: otherResults.firstOrNull()
                    ?: Single.Void("no result available -- error?", null, null)


            override fun collectStatistics(): List<ExecutableStatistics> =
                subResults.map { it.collectStatistics() }.flatten()
        }
    }

    fun getSubresultsWithDifficulties(): List<Single> {
        val res = when (this) {
            is Single.Void -> listOf()
            is Single.Other,
            is Single.Cancelled,
            is Single.Simple -> {
                val satRes = when (this) {
                    is Single.Simple -> this.satResult
                    is Single.Other -> this.satResult
                    else -> error("can't happen")
                }
                when (satRes) {
                    SatResult.SAT,
                    SatResult.UNSAT -> listOf() // we're not reporting difficulties from non UNKNOWN results, so far
                    is SatResult.UNKNOWN ->
                        if (satRes.difficulties != null) {
                            listOf(this as Single)
                        } else {
                            listOf()
                        }
                }
            }
            is Agg -> this.unknownResults.flatMap { it.getSubresultsWithDifficulties() }
        }
        logger.debug {
            "getSubresultsWithDifficulties:\n" +
                    "\t input: $this \n" +
                    "\t output: $res"
        }
        return res
    }

    open fun longToString(): String? = toString()

    companion object {
        private fun solverResultFromSATResult(
            satResult: SatResult,
            checkerInstance: SmtFormulaChecker?,
            query: SmtFormulaCheckerQuery,
            preExecutionStatistics: PreExecutionStatistics?,
            statistics: ResultStatistics?
        ): Single {
            return when (checkerInstance) {
                is SimpleFormulaChecker -> Single.Simple(
                    checkerInstance.solverInstanceInfo,
                    satResult,
                    getValuesResult = null,
                    unsatCore = null,
                    query = query,
                    learnedLits = null,
                    checkSatRuntime = null,
                    preExecutionStatistics = preExecutionStatistics,
                    resultStats = statistics
                )
                else -> Single.Other(
                    satResult,
                    queryInfo = query.info,
                    preExecutionStatistics = preExecutionStatistics,
                    resultStats = statistics
                )
            }
        }

        fun SolverFailedToStart(
            e: InteractingCmdProcessor.SmtSolverFailedToStartException,
            checkerInstance: SmtFormulaChecker?,
            query: SmtFormulaCheckerQuery,
            preExecutionStatistics: PreExecutionStatistics?,
            statistics: ResultStatistics?
        ): Single {
            logger.warn(e) { "solver failed to start; query: ${query.info.name}" }
            return solverResultFromSATResult(SatResult.UNKNOWN.solverFailedToStart(e), checkerInstance, query, preExecutionStatistics, statistics)
        }

        fun SolverOutOfMemory(
            e: InteractingCmdProcessor.SMTSolverOomException,
            checkerInstance: SmtFormulaChecker?,
            query: SmtFormulaCheckerQuery,
            preExecutionStatistics: PreExecutionStatistics?,
            resultStats: ResultStatistics?
        ): Single {
            logger.warn(e) { "solver ran out of memory; query: ${query.info.name}" }
            return solverResultFromSATResult(SatResult.UNKNOWN.solverOutOfMemory(e), checkerInstance, query, preExecutionStatistics, resultStats)
        }


        fun SolverReportedError(
            e: InteractingCmdProcessor.SMTSolverException,
            checkerInstance: SmtFormulaChecker?,
            query: SmtFormulaCheckerQuery,
            preExecutionStatistics: PreExecutionStatistics?,
            resultStats: ResultStatistics?
        ): Single {
            logger.warn(e) { "solver reported error; query: ${query.info.name}" }
            return solverResultFromSATResult(SatResult.UNKNOWN.solverReportedError(e), checkerInstance, query, preExecutionStatistics, resultStats)
        }

        fun LemmaCheckFailed(msg: String, queryInfo: SmtFormulaCheckerQueryInfo, preExecStats: PreExecutionStatistics? = null): SmtFormulaCheckerResult =
            Single.Void(msg, queryInfo, preExecStats)

        /**
         * When the formula checker was interrupted via Java's interrupt functionality.
         * By the logic of [parallel.coroutines.rpcRace] this either means that another solver was faster to give an
           answer or that this solver hit it's external timeout.
         * (It's possible to diagnose an external timeout after-the fact by checking if in the results from the parallel
         *  checker there is a successful result (usually SAT/UNSAT, depending on the approximation status of the
         *  input).
         */
        enum class InterruptReason { LOST_RACE, TIMEOUT, EXTERNAL_TIMEOUT, SKIPPED, SKIPPED_DELAYED }

        fun Interrupted(
            e: Exception?,
            checkerInstance: SmtFormulaChecker?,
            query: SmtFormulaCheckerQuery,
            reason: InterruptReason,
            preExecutionStatistics: PreExecutionStatistics? = null,
            stats: ResultStatistics? = null,
        ): Single {
            val satResult = when (reason) {
                InterruptReason.LOST_RACE -> SatResult.UNKNOWN(SatResult.UnknownReason.LostRace(e), "lost race")
                InterruptReason.TIMEOUT -> SatResult.UNKNOWN(SatResult.UnknownReason.Timeout(e), "timeout")
                InterruptReason.EXTERNAL_TIMEOUT ->
                    SatResult.UNKNOWN(SatResult.UnknownReason.ExternalTimeout(e), "external timeout")
                InterruptReason.SKIPPED -> SatResult.UNKNOWN(SatResult.UnknownReason.Skipped(e), "skipped")
                InterruptReason.SKIPPED_DELAYED ->
                    SatResult.UNKNOWN(SatResult.UnknownReason.SkippedDelayed(e), "skipped delayed")
            }
            return solverResultFromSATResult(satResult, checkerInstance, query, preExecutionStatistics, stats)
        }

        fun ProcessDied(
            e: Exception,
            checkerInstance: SmtFormulaChecker?,
            query: SmtFormulaCheckerQuery,
            preExecutionStatistics: PreExecutionStatistics? = null,
            resultStats: ResultStatistics? = null,
        ): Single {
            logger.warn(e) { "solver process died; query: ${query.info.name}" }
            return solverResultFromSATResult(
                SatResult.UNKNOWN(SatResult.UnknownReason.Error(e), "process died"),
                checkerInstance,
                query,
                preExecutionStatistics,
                resultStats
            )
        }

        fun OtherException(
            e: Exception,
            checkerInstance: SmtFormulaChecker?,
            query: SmtFormulaCheckerQuery,
            preExecutionStatistics: PreExecutionStatistics?,
            resultStats: ResultStatistics?,
        ): Single {
            logger.warn(e) { "solving threw an exception; query: ${query.info.name}" }
            return solverResultFromSATResult(
                SatResult.UNKNOWN(SatResult.UnknownReason.Error(e), "other exception: ${e.javaClass}"),
                checkerInstance,
                query,
                preExecutionStatistics,
                resultStats
            )
        }

        /** Failed to construct any solvers. */
        fun NoSolvers(queryInfo: SmtFormulaCheckerQueryInfo, preExecutionStatistics: PreExecutionStatistics): SmtFormulaCheckerResult =
            Single.Void("failed to construct solvers", queryInfo, preExecutionStatistics)

        /** Failed to construct a solver. */
        fun CantCreateSolver(queryInfo: SmtFormulaCheckerQueryInfo, config: SolverConfig, preExecStats: PreExecutionStatistics) =
            Single.Void("failed to construct solver $config", queryInfo, preExecStats)

        /** used for Config.SkipCallsToSolver ..*/
        fun EmptyResultFromWorkListSolver(): SmtFormulaCheckerResult =
            Single.Void("empty result from worklist solver, something went wrong", null, null)

    }
}

private val logger = Logger(SMTLIBUtilsLoggerTypes.SMT_SMTFORMULACHECKERRESULT)
