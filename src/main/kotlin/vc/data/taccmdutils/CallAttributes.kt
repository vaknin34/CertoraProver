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

package vc.data.taccmdutils

import analysis.icfg.CallGraphBuilder
import vc.data.CallSummary
import vc.data.CoreTACProgram
import vc.data.TACCmd
import datastructures.stdcollections.*
import rules.genericrulecheckers.ViewReentrancyInstrumenting

/**
 * This object contains utility functions for finding different attributes of `CallSummary` commands
 */
object CallAttributes {

    /**
     * @return true if unresolved function
     */
    private fun maybeUnresolvedFunction(summ: CallSummary): Boolean {
        require(summ.sigResolution.size <= 1) { "Expected one sigResolution but got ${summ.sigResolution.size}" }
        val nonFixedCallee = summ.callTarget.any {  it is CallGraphBuilder.CalledContract.SymbolicInput || it is CallGraphBuilder.CalledContract.Unresolved }
        return (summ.sigResolution.isEmpty() || nonFixedCallee)
    }

    /**
     * Returns all unresolved calls in [tacProgram]
     */
    fun getUnresolvedCalls(tacProgram: CoreTACProgram): Set<ViewReentrancyInstrumenting.LCallSummary> =
        tacProgram.analysisCache.graph.commands.mapNotNull {
            val cmd = it.cmd as? TACCmd.Simple.SummaryCmd
            val maybeSummary = cmd?.summ as? CallSummary
            maybeSummary?.let { summ ->
                ViewReentrancyInstrumenting.LCallSummary(it.ptr, summ).takeIf {
                    maybeUnresolvedFunction(maybeSummary)
                }
            }
        }.toSet()

}
