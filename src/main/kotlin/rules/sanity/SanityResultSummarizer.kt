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

import rules.sanity.SanityCheckResult.Companion.join

/**
 * Summarizes the results in [enabledSanityChecksViews] to have results for the parent rule (in case of a parametric rule)
 * and for its children.
 */
data class SanityResultSummarizer(val enabledSanityChecksViews:  List<SanityResultsView<*>>) {
    /**
     * The final sanity-check result of either the parent-rule (in case of a parametric rule) or the base-rule
     * (in case of a non-parametric rule). The result is final in the sense that it accounts for all
     * the sanity checks' sorts that are performed ([enabledSanityChecksViews]), and represents the aggregation
     * of their results.
     */
    val parentResult = enabledSanityChecksViews.map {
        it.aggregatedSanityCheckResult
    }.join(threshold = SanityCheckResultOrdinal.TIMEOUT)

    /**
     * Computes the [SanityCheckResult] of [base] by joining the results from all of the [SanityResultsView]s
     * in [enabledSanityChecksViews].
     * Assumes that all of the [SanityResultsView] in [enabledSanityChecksViews] have an attached result for [base].
     */
    fun joinByBase(base: SanityDPResult): SanityCheckResult =
        enabledSanityChecksViews.map {
            when (it) {
                is SanityResultsView.FunctionDependent<*> -> {
                    it.baseResultToSanityCheckResultMap[base]
                        ?: throw IllegalArgumentException(
                            "expected the base-rule ${
                                base.result.rule.declarationId
                            } to have an aggregated result for the sanity-check ${
                                it.sanityCheckSort.javaClass
                            }"
                        )
                }
                is SanityResultsView.FunctionIndependent<*> -> {
                    it.aggregatedSanityCheckResult
                }
            }
        }.join(threshold = SanityCheckResultOrdinal.TIMEOUT)
}
