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

package rules.sanity

import report.RuleAlertReport
import rules.RuleCheckResult
import solver.SolverResult
import utils.addMatching
import datastructures.stdcollections.*
import log.*

/**
 * Represents the importance of a [SanityCheckResult].
 * Order is important: later is "worse" than earlier.
 */
enum class SanityCheckResultOrdinal {
    PASSED,
    TIMEOUT,
    UNKNOWN,
    ERROR,
    FAILED;

    infix fun join(other: SanityCheckResultOrdinal) =
        if (this > other) {
            this
        } else {
            other
        }

    fun reportString() =
        when(this) {
            PASSED -> {
                "passed"
            }
            TIMEOUT -> {
                "timeout"
            }
            UNKNOWN -> {
                "unknown"
            }
            ERROR -> {
                "error"
            }
            FAILED -> {
                "failed"
            }
        }


    companion object {
        /**
         * Maps this [RuleCheckResult.Single] into a "default" [SanityCheckResultOrdinal].
         * This mapping function is "default" in the sense that it uses this' [RuleCheckResult.Single.result], and
         * maps [SolverResult.UNSAT] to [FAILED] and [SolverResult.SAT] to [PASSED].
         */
        fun RuleCheckResult.Single.toDefaultSanityCheckResultOrdinal() =
            when (this.result) {
                SolverResult.SAT -> {
                    PASSED
                }
                SolverResult.UNSAT -> {
                    FAILED
                }
                SolverResult.TIMEOUT -> {
                    TIMEOUT
                }
                SolverResult.UNKNOWN -> {
                    UNKNOWN
                }
                SolverResult.SANITY_FAIL -> {
                    throw IllegalArgumentException("Didn't expect to have [SolverResult.SANITY_FAIL]")
                }
            }
    }
}

/**
 * Sanity result after aggregating atomic sub-checks' results, where the aggregation of the result itself [ordinal]
 * is done by the severity of the sanity check. [nonErrorMsgs] and [errors] contain the relevant sanity messages to be displayed to the user.
 */
data class SanityCheckResult(
    val nonErrorMsgs: List<SanityCheckNonErrorUIMessage>,
    val ordinal: SanityCheckResultOrdinal,
    val errors: List<RuleAlertReport.Error>
) {
    /**
     * @param threshold Each [SanityCheckNonErrorUIMessage] in the [nonErrorMsgs] attribute of the resulting
     * [SanityCheckResult] will have [SanityCheckNonErrorUIMessage.ordinal] that is at least [threshold];
     * in addition, a necessary condition for [errors] to be non-empty, is [threshold] to be at most
     * [SanityCheckResultOrdinal.ERROR].
     */
    fun join(other: SanityCheckResult, threshold: SanityCheckResultOrdinal = SanityCheckResultOrdinal.PASSED) =
        SanityCheckResult(
            ordinal = this.ordinal join other.ordinal,
            errors = if (SanityCheckResultOrdinal.ERROR >= threshold) {
                this.errors + other.errors
            } else {
                emptyList()
            },
            nonErrorMsgs = buildList {
                addMatching(this@SanityCheckResult.nonErrorMsgs) { it.ordinal >= threshold }
                addMatching(other.nonErrorMsgs) { it.ordinal >= threshold }
            }
        )

    /**
     * Returns all alerts contained in this [SanityCheckResult] which their corresponding ordinal lies in the given
     * range (inclusive on both sides).
     */
    fun allAlertsInRange(
        from: SanityCheckResultOrdinal = SanityCheckResultOrdinal.PASSED,
        to: SanityCheckResultOrdinal = ordinal
    ): RuleAlertReport<*>? =
        buildList {
            addAll(
                nonErrorMsgs.mapNotNull { nonErrorUiMessage ->
                    if (nonErrorUiMessage.ordinal in from..to) {
                        nonErrorUiMessage.nonErrorAlertReport
                    } else {
                        null
                    }
                }
            )
            if (SanityCheckResultOrdinal.ERROR in from..to) {
                addAll(errors)
            }
        }.let { RuleAlertReport(it) }?.also { report ->
            // for testing
            report.asList.forEach { Logger.regression { it.msg } }
        }

    companion object {

        /**
         * The [SanityCheckResult] whose [SanityCheckResult.ordinal] is [SanityCheckResultOrdinal.PASSED],
         * and its other attributes are the empty sets.
         */
        val bottom = SanityCheckResult(emptyList(), SanityCheckResultOrdinal.PASSED, emptyList())

        /**
         * Join over the values of this [Map].
         */
        fun Map<*, SanityCheckResult>.join(
            threshold: SanityCheckResultOrdinal = SanityCheckResultOrdinal.PASSED
        ): SanityCheckResult = this.values.join(threshold)

        /**
         * Join over the elements in this [Collection].
         */
        fun Collection<SanityCheckResult>.join(
            threshold: SanityCheckResultOrdinal = SanityCheckResultOrdinal.PASSED
        ): SanityCheckResult = this.fold(bottom) { joinedResult, currResult ->
            joinedResult.join(currResult, threshold)
        }
    }
}
