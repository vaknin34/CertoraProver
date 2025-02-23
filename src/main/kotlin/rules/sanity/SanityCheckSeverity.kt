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

import rules.RuleCheckResult
import rules.sanity.sorts.SanityCheckSort

/**
 * The "severity" of a [SanityCheckSort] prescribes how to compute the aggregated or summarized result of
 * the underlying sanity-check. Usually, the aggregation of the sanity-results is over sub-rules (or children) of a parametric rule,
 * each of which corresponds to different methods' instantiations.
 *
 * Notably, [Critical] (resp. [Info]) severity level prescribes that the sanity-check of a
 * parametric rule has failed if it has failed for any (rep. for all) of its sub-rules.
 */
sealed class SanityCheckSeverity {

    abstract fun <S : RuleCheckResult.Single> computeSanityCheckResult(
        sanityChecksNonErrorResults: List<DPSuccess<S>>,
        sanityChecksErrorResults: List<DPError>,
        sanityCheckSort: SanityCheckSort<S, *>
    ): SanityCheckResult

    object Critical : SanityCheckSeverity() {
        /**
         * We aggregate independent failures using existential abstraction/quantification
         * for critical level sanity-checks
         */
        override fun <S : RuleCheckResult.Single> computeSanityCheckResult(
            sanityChecksNonErrorResults: List<DPSuccess<S>>,
            sanityChecksErrorResults: List<DPError>,
            sanityCheckSort: SanityCheckSort<S, *>
        ): SanityCheckResult {
            return SanityCheckResult(
                nonErrorMsgs = sanityChecksNonErrorResults.map(sanityCheckSort::nonErrorUIMessageOf),
                errors = sanityChecksErrorResults.flatMapTo(mutableListOf()) { it.result.ruleAlerts.asList },
                ordinal = sanityChecksNonErrorResults
                    .map { sanityCheckSort.checkResultToSanityResultOrd(it) }
                    .let { ordinals ->
                        when {
                            ordinals.any { it == SanityCheckResultOrdinal.FAILED } -> {
                                SanityCheckResultOrdinal.FAILED
                            }
                            sanityChecksErrorResults.isNotEmpty() -> {
                                SanityCheckResultOrdinal.ERROR
                            }
                            ordinals.any { it == SanityCheckResultOrdinal.TIMEOUT } -> {
                                SanityCheckResultOrdinal.TIMEOUT
                            }
                            ordinals.any { it == SanityCheckResultOrdinal.UNKNOWN } -> {
                                SanityCheckResultOrdinal.UNKNOWN
                            }
                            ordinals.all { it == SanityCheckResultOrdinal.PASSED } -> {
                                SanityCheckResultOrdinal.PASSED
                            }
                            else -> {
                                throw IllegalStateException(
                                    "Unexpected sanity check results non error " +
                                            "$sanityChecksNonErrorResults and error " +
                                            "$sanityChecksErrorResults for sort " +
                                            "$sanityCheckSort in $this"
                                )
                            }
                        }
                    }
            )
        }
    }

    /**
     * We aggregate independent failures using universal abstraction/quantification
     * for info level sanity checks
     */
    object Info : SanityCheckSeverity() {
        override fun <S : RuleCheckResult.Single> computeSanityCheckResult(
            sanityChecksNonErrorResults: List<DPSuccess<S>>,
            sanityChecksErrorResults: List<DPError>,
            sanityCheckSort: SanityCheckSort<S, *>
        ): SanityCheckResult {
            return SanityCheckResult(
                nonErrorMsgs = sanityChecksNonErrorResults.map(sanityCheckSort::nonErrorUIMessageOf),
                errors = sanityChecksErrorResults.flatMapTo(mutableListOf()) { it.result.ruleAlerts.asList },
                ordinal = sanityChecksNonErrorResults
                    .map { sanityCheckSort.checkResultToSanityResultOrd(it) }
                    .let { ordinals ->
                        when {
                            sanityChecksErrorResults.isNotEmpty() -> {
                                SanityCheckResultOrdinal.ERROR
                            }
                            ordinals.any { it == SanityCheckResultOrdinal.TIMEOUT } -> {
                                SanityCheckResultOrdinal.TIMEOUT
                            }
                            ordinals.any { it == SanityCheckResultOrdinal.UNKNOWN } -> {
                                SanityCheckResultOrdinal.UNKNOWN
                            }
                            ordinals.any { it == SanityCheckResultOrdinal.PASSED } -> {
                                SanityCheckResultOrdinal.PASSED
                            }
                            ordinals.all { it == SanityCheckResultOrdinal.FAILED } -> {
                                SanityCheckResultOrdinal.FAILED
                            }
                            else -> {
                                throw IllegalStateException(
                                    "Unexpected sanity check results non error " +
                                            "$sanityChecksNonErrorResults and error " +
                                            "$sanityChecksErrorResults for sort " +
                                            "$sanityCheckSort in $this"
                                )
                            }
                        }
                    }

            )
        }
    }
}
