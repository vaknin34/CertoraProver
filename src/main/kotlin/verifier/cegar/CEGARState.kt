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

import datastructures.stdcollections.toList
import smtlibutils.cmdprocessor.SmtFormulaCheckerQuery
import smtlibutils.data.*
import smt.CEGARConfig
import smt.ConstraintChooserEnum
import solver.SolverConfig
import vc.gen.LExpVC
import kotlin.time.Duration
import java.util.concurrent.atomic.AtomicBoolean

/**
 * The state of a running CEGAR solving.
 * Consists of some fixed state (the [vc], [LIAquery], [NIAquery] and [config]), the logger and synchronization
 * mechanisms. [running] is used to signal upcoming termination, [liaModelQueue] manages the counterexample candidates
 * that are to be checked and [learnedClauses] stores clauses that were learned from the [LIAquery].
 */
class CEGARState(
    val vc: LExpVC,
    val script: FactorySmtScript,
    val LIAquery: SmtFormulaCheckerQuery,
    val NIAquery: SmtFormulaCheckerQuery,
    val config: CEGARConfig,
) {
    val statsLogger: CEGARStatsLogger = CEGARStatsLogger()
    val running: AtomicBoolean = AtomicBoolean(false)

    fun logResult(
        type: CEGARStatsLogger.LogEntryType,
        sc: SolverConfig,
        duration: Duration,
        result: SatResult,
        queryName: String,
        cex: List<SmtExp>? = null,
        cc: ConstraintChooserEnum? = null,
    ) = statsLogger.log(
        type = type,
        sc = sc,
        duration = duration,
        queryName = queryName,
        result = result,
        cex = cex,
        cc = cc,
    )

    val liaModelQueue: LIAModelQueue = LIAModelQueue()

    // Any learned clauses, usually blocking clauses eliminating spurious counter-examples or general lemmas found
    // by solvers in learning mode.
    private val learnedClauses: MutableList<SmtExp> = mutableListOf()

    /**
     * Blocks the given (spurious) counterexample by adding its negation to the learned clauses.
     */
    fun blockCEX(cex: List<SmtExp>) {
        synchronized(learnedClauses) {
            learnedClauses.add(script.not(script.and(cex)))
        }
    }

    /**
     * Adds the given list of lemmas to the learned clauses.
     */
    fun addLearned(learned: List<SmtExp>) {
        synchronized(learnedClauses) {
            learnedClauses.addAll(learned)
        }
    }

    /**
     * Retrieves the learned clauses starting from the given index. Returns a copy of this sublist to avoid concurrency
     * issues that occur when only a view on that list is used outside the synchronized block.
     */
    fun getLearned(fromIndex: Int): List<SmtExp> {
        synchronized(learnedClauses) {
            return learnedClauses.subList(fromIndex, learnedClauses.size).toList()
        }
    }

    /**
     * Check if there are new learned clauses after the given index. Essentially equivalent to
     * `getLearned(fromIndex).isNotEmpty()`, but faster.
     */
    fun hasNewLearned(fromIndex: Int): Boolean {
        synchronized(learnedClauses) {
            return learnedClauses.size > fromIndex
        }
    }
}
