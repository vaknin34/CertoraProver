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

package vc.data

import spec.TACSymbolAllocation
import spec.cvlast.CVLParam
import tac.CallId

/**
 * Represents the compiled body of an "expression" summary.  They are used to ferry information from CVL-Compilation
 * time to inlining time.  Since a single summary is potentially inlined many times, this represents a sort of "template"
 * for the generated summary implementation.
 *
 * @property outVars the [CVLParam]s which have been generated to hold the output of the summary
 *
 * @property allocatedTACSymbols holds variables allocated for any identifier that might appear in the CVL body of the
 * summary
 *
 * @property body the compiled body of the function; contains a single root
 *
 * @require [allocatedTACSymbols] contains [outVar] and all variables read by [body]
 */
data class CompiledExpressionSummary(
    val outVars: List<CVLParam>,
    val allocatedTACSymbols: TACSymbolAllocation,
    val body: CVLTACProgram,
    val summaryName: String,
    val callId: CallId
) {
    override fun toString() = summaryName
}
