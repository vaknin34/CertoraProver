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
import spec.cvlast.SpecType

/**
 * Container for [results] - contains all the sanity and base rules' results.
 * Possibly, the container may include results of multiple, different sanity-checks.
 *
 * One can filter the results in this [SanityResultsContainer] w.r.t. a given sanity-check ([SanityCheckSort]) through
 * the [narrow] functions, which would return a corresponding [SanityResultsView].
 */
class SanityResultsContainer(val results: List<SanityDPResult>) {

    /**
     * Base-rules' results. These are the results of the rules whose sanity is being checked.
     */
    val baseResults: List<SanityDPResult> = results.filter {
        it.result.rule.ruleType.let { ruleType ->
            ruleType is SpecType.Single.FromUser ||
                ruleType is SpecType.Single.EnvFree ||
                ruleType is SpecType.Single.InvariantCheck ||
                ruleType is SpecType.Single.BuiltIn
        }
    }

    /**
     * Sanity-rules' results. These are the results of the rules generated to check the sanity
     * of the base rules in [baseResults].
     */
    val sanityCheckResults: List<SanityDPResult> = results.filterNot { it in baseResults }

    init {
        check(sanityCheckResults.all { it.result.rule.ruleType is SpecType.Single.GeneratedFromBasicRule }) {
            "Expected all sanity check results to have rules of type [SpecType.Single.GeneratedFromBasicRule], but got ${
                sanityCheckResults.filterNot { it.result.rule.ruleType is SpecType.Single.GeneratedFromBasicRule }
                    .joinToString(prefix = "[", postfix = "]", separator = ",") { badRuleResult ->
                        "${badRuleResult.result.rule.declarationId} : ${badRuleResult.result.rule.ruleType}"
                    }
            }"
        }
    }

    /**
     * Maps each sanity-check sort in [sanityChecksSorts] into its corresponding view ([SanityResultsView]).
     */
    fun <S : RuleCheckResult.Single> narrow(
        sanityChecksSorts: List<SanityCheckSort<S, *>>
    ): List<SanityResultsView<S>> = sanityChecksSorts.map(::narrow)

    /**
     * Returns a view ([SanityResultsView]) of
     * this [SanityResultsContainer] w.r.t. the given sanity-check sort ([sanityCheckSort]).
     */
    fun <S : RuleCheckResult.Single> narrow(
        sanityCheckSort: SanityCheckSort<S, *>
    ): SanityResultsView<S> = when (sanityCheckSort) {
        is SanityCheckSort.FunctionIndependent -> {
            narrow(sanityCheckSort)
        }
        is SanityCheckSort.FunctionDependent -> {
            narrow(sanityCheckSort)
        }
    }

    /**
     * Given the function-independent sanity-check sort ([sanityCheckSort]),
     * returns a corresponding view ([SanityResultsView.FunctionIndependent]) of
     * this [SanityResultsContainer].
     */
    fun <S : RuleCheckResult.Single> narrow(
        sanityCheckSort: SanityCheckSort.FunctionIndependent<S, *>
    ): SanityResultsView.FunctionIndependent<S> = sanityCheckSort.toSanityResultsView(
        _sanityCheckResults = sanityCheckResults
    )

    /**
     * Given the function-dependent sanity-check sort ([sanityCheckSort]),
     * returns a corresponding view ([SanityResultsView.FunctionDependent]) of
     * this [SanityResultsContainer].
     */
    fun <S : RuleCheckResult.Single> narrow(
        sanityCheckSort: SanityCheckSort.FunctionDependent<S, *>
    ): SanityResultsView.FunctionDependent<S> = sanityCheckSort.toSanityResultsView(
        _baseResults = baseResults,
        _sanityCheckResults = sanityCheckResults
    )

}
