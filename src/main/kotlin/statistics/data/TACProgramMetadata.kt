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

package statistics.data

import datastructures.stdcollections.*
import kotlinx.serialization.Serializable
import verifier.NameObject
import verifier.RuleAndSplitIdentifier
import verifier.splits.SplitAddress

/**
 * Metadata for a tac program, for use in the region after [LeinoWP].
 * Contains information on which CVL rule it was created for, whether it's a split, etc.
 *
 * Let's not pull in big dependencies here. (E.g. had problems with [CVLRule], which was handed around all over the
 * place and e.g. has the full AST of a rule, apparently.)
 *
 * Once we have a nice rule identifier like "rule tree path" or so, it could go here (maybe even replace the
 * [NameObject]).
 *
 * I'm not making this part of [TACProgram] because a) it would be a much bigger change, b) its limited usage scope.
 */
@Serializable
data class TACProgramMetadata(
    val ruleAndSplitId: RuleAndSplitIdentifier,
    // this is a bit of a pain -- it's used deep in the verifier, when the result is built; all I know is I don't want
    // to pipe the whole rule through ..
    val findReachabilityFailureSourceShouldCheckRule: Boolean = false,
    val cvlVarsInAsserts: List<String> = emptyList(),
    val cvlVars: List<String> = emptyList(),
    val isSanityRule: Boolean = false,
) {
    fun updateSplitAddress(splitAddress: SplitAddress) =
        copy(ruleAndSplitId = ruleAndSplitId.copy(splitAddress = splitAddress))
}
