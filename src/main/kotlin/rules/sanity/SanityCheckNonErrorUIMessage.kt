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
import rules.dpgraph.DPResult

/**
 * Encapsulates a UI message that describes a non-error result of a rule-sanity check.
 *
 * [nonErrorAlertReport] a non error [RuleAlertReport.Single] containing the result description
 * [ordinal] the ordinal of the result (must not be [SanityCheckResultOrdinal.ERROR])
 */
data class SanityCheckNonErrorUIMessage(
    val nonErrorAlertReport: RuleAlertReport.Single<*>,
    val ordinal: SanityCheckResultOrdinal
) {

    init {
        check(ordinal != SanityCheckResultOrdinal.ERROR) {
            "Expected [ordinal] to be a non-error SanityCheckResultOrdinal"
        }
        check(nonErrorAlertReport !is RuleAlertReport.Error) {
            "Expected [nonErrorAlertReport] to be a non-error RuleAlertReport"
        }
    }
}

/**
 * Determines the format and content of the UI messages that describe
 * the non-error results of rule-sanity checks, all of which have the same underlying [SanityCheckSort].
 */
class SanityCheckNonErrorUIMessageFormatter<in G>(
    val rawMsg: String,
    /**
     * Gets as input: ([SanityCheckResultOrdinal], "sanity sub-check group" ([G]), extraDetails ([String]), raw message).
     * Returns a formatted message
     */
    val rawMsgFormatter: (SanityCheckResultOrdinal, G, String, String) -> String
) {

    /**
     * Returns the non-error, formatted UI message of the underlying [SanityCheckSort], for
     * the given [sanityCheckResultOrdinal].
     */
    fun nonErrorUIMessageOf(
        sanityCheckResultCTyp: DPResult.ComputationalType,
        sanityCheckSeverity: SanityCheckSeverity,
        sanityCheckResultOrdinal: SanityCheckResultOrdinal,
        sanitySubCheckGroup: G,
        details: Result<String>
    ): SanityCheckNonErrorUIMessage {
        val msg = "${sanityCheckResultCTyp.toUIStringOrNull()?.let { "$it: " }.orEmpty()}${
            rawMsgFormatter(sanityCheckResultOrdinal, sanitySubCheckGroup, details.getOrElse { "" }, rawMsg)
        }"

        val ruleAlertReport: RuleAlertReport.Single<*> = when (sanityCheckResultOrdinal) {
            SanityCheckResultOrdinal.PASSED -> {
                RuleAlertReport.Info(msg)
            }
            SanityCheckResultOrdinal.FAILED, SanityCheckResultOrdinal.UNKNOWN, SanityCheckResultOrdinal.TIMEOUT -> {
                when (sanityCheckSeverity) {
                    is SanityCheckSeverity.Critical -> {
                        RuleAlertReport.Warning(msg)
                    }
                    is SanityCheckSeverity.Info -> {
                        RuleAlertReport.Info(msg)
                    }
                }
            }
            SanityCheckResultOrdinal.ERROR -> {
                throw IllegalArgumentException(
                    "Did not expect to get an ERROR sanity check result ordinal"
                )
            }
        }

        return SanityCheckNonErrorUIMessage(
            nonErrorAlertReport = ruleAlertReport,
            ordinal = sanityCheckResultOrdinal
        )
    }
}
