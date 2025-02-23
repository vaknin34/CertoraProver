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

package solver

import smtlibutils.cmdprocessor.SmtFormulaCheckerResult
import smtlibutils.data.SatResult
import utils.AmbiSerializable
import utils.KSerializable

/** redundancy: [SatResult], [SmtFormulaCheckerResult] */
@KSerializable
enum class SolverResult(
    /**
     * Determines the order by which the rules' results appear in the table shown at the
     * HTML report (see [JSONForHtmlResults]). The lower the value, the higher the precedence in the table.
     */
    val resultsTableOrdinal: Int,
    /**
     * Describes how "worse" the result is. Higher the ordinal, the "worse" the result.
     */
    val severityOrdinal: Int
): AmbiSerializable {

    SAT(2, 4),
    UNSAT(3, 0),
    UNKNOWN(0, 2),
    TIMEOUT(1, 1),
    SANITY_FAIL(4, 3)
    ;

    enum class JSONRepresentation {
        FAIL, SUCCESS, UNKNOWN, TIMEOUT, SANITY_FAIL;

        // This is an abomination and it should go. JSONRepresentation should be the final representation anywhere
        fun toSolverResult(): SolverResult {
            return when (this) {
                FAIL -> SolverResult.SAT
                SUCCESS -> SolverResult.UNSAT
                UNKNOWN -> SolverResult.UNKNOWN
                TIMEOUT -> SolverResult.TIMEOUT
                SANITY_FAIL -> SolverResult.SANITY_FAIL
            }
        }
    }

    enum class FeatureRepresentation {
        YES, NO, UNKNOWN, TIMEOUT;
    }

    fun toCSVRepresentation(): String {
        return when (this) {
            SAT -> "X"
            UNSAT -> "V"
            UNKNOWN -> "?"
            SANITY_FAIL -> "!"
            TIMEOUT -> "T"
        }
    }

    fun toJSONRepresentation(satIsGood: Boolean = false): String {
        val fail = JSONRepresentation.FAIL.name
        val success = JSONRepresentation.SUCCESS.name

        return when (this) {
            SAT -> if (satIsGood) { success } else { fail } 
            UNSAT -> if (satIsGood) { fail } else { success }
            UNKNOWN -> JSONRepresentation.UNKNOWN.name
            TIMEOUT -> JSONRepresentation.TIMEOUT.name
            SANITY_FAIL -> JSONRepresentation.SANITY_FAIL.name
        }
    }

    /**
     * Joins this [SolverResult] with [other] by returning the maximal element w.r.t.
     * [SolverResult.severityOrdinall].
     */
    infix fun join(other: SolverResult): SolverResult =
        if (this.severityOrdinal > other.severityOrdinal) {
            this
        } else {
            other
        }

    companion object {
        fun fromJSONRepresentationString(s: String): SolverResult {
            return JSONRepresentation.valueOf(s).toSolverResult()
        }

        /**
         * Aggregates the list of solver-results [solverResults] into a solver-result,
         * using the join operation.
         */
        fun join(solverResults: List<SolverResult>): SolverResult {
            return solverResults.fold(UNSAT) { result, currentResult ->
                currentResult join result
            }
        }

        fun fromCheckerResult(smtFormulaCheckerResult: SmtFormulaCheckerResult): SolverResult {
            return when (smtFormulaCheckerResult.satResult) {
                SatResult.UNSAT -> UNSAT
                is SatResult.SAT -> SAT
                is SatResult.UNKNOWN ->
                    if (smtFormulaCheckerResult.hasTimeoutOrOom()) {
                        TIMEOUT
                    } else {
                        UNKNOWN
                    }
            }

        }
    }

    fun isSuccess(): Boolean = this == UNSAT
}
