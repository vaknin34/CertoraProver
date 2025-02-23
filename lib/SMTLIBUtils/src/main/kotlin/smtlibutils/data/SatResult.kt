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

package smtlibutils.data

import kotlinx.coroutines.flow.*
import log.*
import smtlibutils.cmdprocessor.CmdProcessor
import smtlibutils.cmdprocessor.InteractingCmdProcessor
import smtlibutils.cmdprocessor.SmtFormulaCheckerResult
import smtlibutils.cmdprocessor.SolverInstanceInfo
import utils.*

sealed class SatResult: java.io.Serializable {
    object UNSAT : SatResult() {
        override fun toString(): String = "UNSAT"
        private fun readResolve(): Any = UNSAT
        override fun hashCode(): Int  = utils.hashObject(this)

    }

    /**
     * @param infoString an optional, pretty description of the problem that was encountered
     */
    data class UNKNOWN(
        val reason: UnknownReason,
        val infoString: String? = null,
        val difficulties: Difficulties? = null
    ) : SatResult() {

        fun withReason(reason: UnknownReason): UNKNOWN {
            if (this.reason == UnknownReason.NoAnswers && reason is UnknownReason.Other) {
                return this
            }
            check(this.reason is UnknownReason.Other)
            return this.copy(reason = reason)
        }

        override fun toString(): String = "SatResult.UNKNOWN(" +
                "\n\t$reason" +
                (infoString?.let { "\n\tinfoString: $it" }.orEmpty()) +
                (difficulties?.let { "\n\tdifficulties: $it" }.orEmpty()) +
                "\n\t)"

        /** If the result is Unknown because solver threw an exception, the exception should be stored here.
         * Since [UnknownReason.ExternalTimeout] is also considered abnormal, we're also reporting it as a solver
         * execption. */
        val exceptionFromSolver: Exception? get() = when(reason) {
            is UnknownReason.Error -> reason.e
            is UnknownReason.ExternalTimeout -> reason.e
            is UnknownReason.Timeout -> reason.e
            is UnknownReason.LostRace -> reason.e
            else -> null
        }


        fun withDifficulties(difficulties: Difficulties): UNKNOWN {
            check(this.difficulties == null)
            { "Should not overwrite existing difficulties in this UNKNOWN result ($this)." }
            return this.copy(difficulties = difficulties)
        }

        companion object {
            fun solverFailedToStart(e: InteractingCmdProcessor.SmtSolverFailedToStartException): SatResult {
                return UNKNOWN(
                    UnknownReason.FailedToStart(e),
                    "Failed to start solver process: \"${e.solverInstanceInfo.actualCommand}\""
                )
            }


            fun solverOutOfMemory(e: InteractingCmdProcessor.SMTSolverOomException): SatResult {
                return UNKNOWN(
                    UnknownReason.OutOfMemory(e),
                    "solver out of memory (cmd line: ${e.cmdLine})"
                )
            }

            fun solverReportedError(
                e: Exception,
            ): SatResult {
                return UNKNOWN(
                    UnknownReason.Error(e), "solverReportedError(..)"
                )
            }
        }
    }

    object SAT : SatResult() {
        override fun toString(): String = "SAT"
        private fun readResolve(): Any = SAT
        override fun hashCode(): Int  = utils.hashObject(this)

    }

    companion object {
        val validSatResponses: Set<String> = setOf("sat", "unsat", "unknown", "timeout")

        /**
         * @param allowBogusLines some solvers (looking at you, alt-ergo) print some stuff in addition to the sat result
         *      in response to check-sat -- set this to true if these should be ignored silently
         */
        suspend fun fromCheckSatOutput(
            linesIn: Flow<String>,
            solverInstanceInfo: SolverInstanceInfo,
            optionsIn: CmdProcessor.Options = CmdProcessor.Options.Default
        ): SatResult {
            val options: CmdProcessor.Options =
                if (solverInstanceInfo != SolverInstanceInfo.None) {
                    solverInstanceInfo.options
                } else {
                    optionsIn
                }

            val lines =
                if (solverInstanceInfo != SolverInstanceInfo.None)
                    solverInstanceInfo.solverConfig.solverInfo.preprocessCheckSatOutput(linesIn)
                else
                    linesIn

            logger.debug { "entering fromCheckSatOutput" }
            val maybeBogusLines = lines.onEach { logger.debug { "lines: $it" } }

            val allowBogusLines: Boolean = options.oneOffSolver
            logger.debug { "allowBogusLines: $allowBogusLines" }
            val nonBogusLines =
                if (allowBogusLines) {
                    maybeBogusLines.filter { it in validSatResponses }
                } else {
                    maybeBogusLines.filter { it != "success" }
                }.onEach {
                    logger.debug { "nonBogusLines: $it" }
                }

            // Note that we need to collect everything from the flow, because our caller may have onEach listeners that
            // must be invoked.
            var count = 0
            var satResultLine: String? = null
            nonBogusLines.collect { line ->
                ++count
                if (count == 2) {
                    val info =
                        "Got more than one-line answer to a check-sat query."
                    logger.warn { info }
                }
                if (satResultLine == null && line in validSatResponses) {
                    satResultLine = line
                }
            }
            if (count == 0) {
                return if (options.noAnswers) {
                    // this can happen e.g. when we're running just a PrintingCmdProcessor
                    UNKNOWN(UnknownReason.NoAnswers)
                } else {
                    val info =
                        "Expected a proper check-sat answer from solver $solverInstanceInfo " +
                                "(proper answers are $validSatResponses)."
                    logger.warn { info }
                    UNKNOWN(UnknownReason.Other(info))
                }
            }

            logger.debug { "satResultLine: $satResultLine" }

            return when (satResultLine) {
                "unsat" -> UNSAT
                "sat" -> SAT
                "unknown" -> UNKNOWN(UnknownReason.Other(), null)
                // apparently, (at least) z3 sometimes returns timeout here (observed with -T:50 option (hard timeout))
                "timeout" -> UNKNOWN(UnknownReason.TimeoutSolverProcess, null)
                null -> {
                    val info = "Got no valid response to check-sat query."
                    logger.warn { info }
                    UNKNOWN(UnknownReason.Other(info))
                }
                else -> {
                    val info = "Unexpected checksat response: \"$satResultLine\""
                    logger.warn { info }
                    UNKNOWN(UnknownReason.Other(info))
                }
            }
        }
    }

    sealed class UnknownReason {

        /**
         * true if the unknown result was due to a timeout -- not totally clear about the logics here yet...
         * */
        val isTimeout: Boolean
            get() = when (this) {
                is Other,
                is Overapproximation,
                is Underapproximation,
                NoAnswers,
                NoSolvers,
                is Error,
                is OutOfMemory,
                is LostRace,
                is Skipped,
                is SkippedDelayed,
                is FailedToStart,
                is Interrupted -> false

                is Timeout,
                is ExternalTimeout,
                TimeoutSolverProcess,
                TimeoutSolverQuery -> true
            }

        val isOom: Boolean
            get() = when (this) {
                is Other,
                is Overapproximation,
                is Underapproximation,
                NoAnswers,
                NoSolvers,
                is Timeout,
                is ExternalTimeout,
                TimeoutSolverProcess,
                TimeoutSolverQuery,
                is Error,
                is LostRace,
                is Skipped,
                is SkippedDelayed,
                is FailedToStart,
                is Interrupted -> false

                is OutOfMemory -> true
            }

        val shouldBeReportedAsError: Boolean
            get() = when (this) {
                is Other,
                is Overapproximation,
                is Underapproximation,
                NoAnswers,
                is Timeout,
                is ExternalTimeout,
                TimeoutSolverProcess,
                TimeoutSolverQuery,
                is Interrupted,
                is LostRace,
                is Skipped,
                is SkippedDelayed -> false

                is FailedToStart,
                NoSolvers,
                is Error,
                is OutOfMemory -> true
            }

        data class Timeout(val e: Exception?) : UnknownReason() {
            override fun toString(): String {
                return "Timeout"
            }
        }

        data class LostRace(val e: Exception?) : UnknownReason() {
            override fun toString(): String {
                return "LostRace"
            }
        }

        data class ExternalTimeout(val e: Exception?) : UnknownReason() {
            override fun toString(): String {
                return "ExternalTimeout"
            }
        }

        data class Skipped(val e: Exception?) : UnknownReason() {
            override fun toString(): String {
                return "Skipped"
            }
        }

        data class SkippedDelayed(val e: Exception?) : UnknownReason() {
            override fun toString(): String {
                return "SkippedDelayed"
            }
        }

        /** the solver has a per-process time out set (e.g. z3 -T:1 ) and has shut down because of it */
        object TimeoutSolverProcess : UnknownReason()

        /** the solver has a per-query time out set (e.g. z3 -t:1 ) and has returned unknown because of it */
        object TimeoutSolverQuery : UnknownReason() {
            override fun toString(): String {
                return "SolverTimeout"
            }
        }

        /** returned by checkers that aren't solvers, e.g. the ones that just print to a file */
        object NoAnswers : UnknownReason()

        /** Failed to run any solvers at all. */
        object NoSolvers : UnknownReason()

        data class Other(val info: String? = null) : UnknownReason() {
            fun withInfo(info: String): Other {
                check(this.info == null)
                check(!info.contains("timeout")) { "failed to detect a timeout?" }
                return Other(info)
            }
        }

        data class Overapproximation(val wrapped: SmtFormulaCheckerResult.Single) : UnknownReason() {
            override fun toString(): String {
                return "Overapproximation(${wrapped.satResult})"
            }
        }

        data class Underapproximation(val wrapped: SmtFormulaCheckerResult) : UnknownReason() {
            override fun toString(): String {
                return "Underapproximation(${wrapped.satResult})"
            }
        }

        data class Error(val e: Exception) : UnknownReason() {
            override fun toString(): String {
                return "Error(${e.message ?: e.javaClass})"
            }
        }

        data class OutOfMemory(val e: InteractingCmdProcessor.SMTSolverOomException) : UnknownReason() {
            override fun toString(): String {
                return "OutOfMemory(${e.cmdLine})"
            }
        }

        data class FailedToStart(val e: InteractingCmdProcessor.SmtSolverFailedToStartException) : UnknownReason() {
            override fun toString(): String {
                return "FailedToStart(${e.solverInstanceInfo.actualCommand})"
            }
        }

        /**
         * The run was interrupted and therefore did not exit cleanly.  No further information is available from the run
         */
        object Interrupted : UnknownReason()

        companion object {
            private const val unknownGetInfoPrefix = "(:reason-unknown "
            private const val msg = "(get-info :reason-unknown) returned:"

            /**
             * string ops reason: some lightweight parsing
             */
            fun parseFromGetInfo(lines: List<String>): UnknownReason {
                val nonSuccessLines = lines.filter { it != "success" }
                if (nonSuccessLines.isNotEmpty() &&
                    nonSuccessLines.first().let { it.startsWith(unknownGetInfoPrefix) && it.endsWith(")") }
                ) {
                    return when (nonSuccessLines.first()
                        .substring(unknownGetInfoPrefix.length, nonSuccessLines.first().length - 1)) {
                        "timeout" -> TimeoutSolverQuery
                        "\"timeout\"" -> TimeoutSolverQuery
                        else -> Other("$msg: ${nonSuccessLines.joinToString(" ")}")
                    }
                }
                return Other((listOf(msg) + nonSuccessLines).joinToString("\n"))
            }
        }
    }
}

private val logger = Logger(SMTLIBUtilsLoggerTypes.SMTLIBUTILS)
