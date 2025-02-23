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

import log.*
import smtlibutils.data.ISmtScript
import smtlibutils.data.SatResult
import smtlibutils.statistics.PreExecutionStatistics
import utils.TimeSinceStart
import java.io.Closeable

/**
 * This function type is used to postprocess a checker result immediately after the check.
 * Most importantly, it is executed while the current scope of the solver is still intact, i.e., before calling `(pop)`.
 */
typealias ResultPostprocessor = suspend (SmtFormulaCheckerResult.Single.Simple, SmtQueryProcessorContext) -> SmtFormulaCheckerResult.Single.Simple

/**
 * Simple interface to check formulas in a one-off manner
 */
interface SmtFormulaChecker : Closeable {

    /** *
     * Call this in a `.use { it.check(..) }` block to make use of the [Closeable]
     */
    suspend fun check(
        query: SmtFormulaCheckerQuery,
        preExecStats: PreExecutionStatistics? = null,
        startTime: TimeSinceStart = TimeSinceStart(),
    ): SmtFormulaCheckerResult

    suspend fun checkSat(
        baseQuery: SmtFormulaCheckerQuery,
        preExecStats: PreExecutionStatistics? = null
    ): SmtFormulaCheckerResult.Single =
        SmtFormulaCheckerResult.Single.Void("not implemented", baseQuery.info, preExecStats)

    companion object {
        /**
         * Executes each checker in [checkers] in order, and returns the first result that is not [SatResult.UNKNOWN]
         * See also [SequentialFormulaChecker].
         */
        suspend fun sequential(
            script: ISmtScript,
            options: CmdProcessor.Options,
            checkers: List<SmtFormulaChecker>,
            dumpFile: String?
        ): SmtFormulaChecker =
            SequentialFormulaChecker(checkers).let { checker ->
                if (dumpFile != null) {
                    prependPrinter(
                        script,
                        options,
                        checker,
                        dumpFile
                    )
                } else {
                    checker
                }
            }


        suspend fun prependPrinter(
            script: ISmtScript,
            options: CmdProcessor.Options,
            formulaChecker: SmtFormulaChecker,
            dumpFile: String
        ): SequentialFormulaChecker {
            val printer = PrintingFormulaChecker.printer(
                script,
                dumpFile = dumpFile,
                options = options
            )
            return SequentialFormulaChecker(printer, formulaChecker)
        }
    }
}

/**
 * Executes each checker in [checkers] in order, and returns the first result that is not [SatResult.UNKNOWN]
 * */
class SequentialFormulaChecker(val checkers: List<SmtFormulaChecker>) : SmtFormulaChecker {
    constructor(vararg checkers: SmtFormulaChecker) : this(checkers.toList())

    init {
        check(checkers.size > 1)
        { "no sense in making a SequentialFormulaChecker with only one checker" }
    }

    override suspend fun check(
        query: SmtFormulaCheckerQuery,
        preExecStats: PreExecutionStatistics?,
        startTime: TimeSinceStart
    ): SmtFormulaCheckerResult.Agg.SequentialResult {
        var result: SmtFormulaCheckerResult? = null
        val unknownResults: MutableList<SmtFormulaCheckerResult> = mutableListOf()
        checkers.forEach { checker ->
            if (result == null) {
                val res = try {
                    checker.check(query, preExecStats, startTime)
                } catch (e: SimpleFormulaChecker.IOExceptionWithStats) {
                    SmtFormulaCheckerResult.ProcessDied(e.original, checker, query, preExecStats, e.s)
                }
                if (checker !is PrintingFormulaChecker) {
                    if (res.satResult is SatResult.UNKNOWN) {
                        logger.debug { "$checker failed to give a result" }
                        unknownResults.add(res)
                    } else {
                        logger.debug { "$checker gave $res" }
                        result = res
                    }
                }
            } else {
                /* already have a result, skip other checkers */
            }
        }
        return SmtFormulaCheckerResult.Agg.SequentialResult(this, result, unknownResults, query.info)
    }

    override fun close() {
        checkers.forEach { it.close() }
    }

    override fun toString(): String {
        return "SequentialFormulaChecker($checkers)"
    }
}

private val logger = Logger(SMTLIBUtilsLoggerTypes.SMTLIBUTILS)

