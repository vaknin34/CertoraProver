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

package rules.genericrulecheckers.helpers

import analysis.CmdPointer
import tac.Tag
import vc.data.SimplePatchingProgram
import vc.data.TACCmd
import vc.data.TACSymbol
import vc.data.asTACExpr
import datastructures.stdcollections.*


object ReachabilityTrackingManager {
    /**
     * This is used to add variables to check whether a certain pointer was reached.
     * Initialization of the tracking will happen in [init], which will be right after root most of the time.
     * For each pointer in [trackingLocs], a new boolean Var will be declared. It will be true if the pointer was
     * reached.
     * [suffix] is an optional parameter used to uniquify the tracking from others.
     * @param[patchingProgram] - the program to add the tracking to.
     * @param[init] - location where the tracking variables are initialized.
     * @param[trackingLocs] - locations to track
     * @param[suffix] - suffix for the tracking variable names.
     * @return list of pointers per [trackingLocs] pointer.
     */
    fun addReachedTracking(patchingProgram: SimplePatchingProgram,
                           init: CmdPointer,
                           trackingLocs: List<CmdPointer>,
                           suffix: String): List<TACSymbol.Var> {
        val vars = trackingLocs.indices.map { i -> TACSymbol.Var("tracking${suffix}_$i", Tag.Bool) }
        with(patchingProgram) {
            addVarDecls(vars.toSet())
            replaceCommand(init, vars.map {
                TACCmd.Simple.AssigningCmd.AssignExpCmd(it, false.asTACExpr)
            })
            vars.zip(trackingLocs).forEach { (v, ptr) ->
                replaceCommand(ptr, listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(v, true.asTACExpr)
                ))
            }
        }
        return vars
    }

}
