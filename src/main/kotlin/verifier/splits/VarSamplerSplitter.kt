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

package verifier.splits

import analysis.CmdPointer
import analysis.opt.intervals.ExtBig.Companion.asExtBig
import analysis.opt.intervals.Intervals
import utils.*
import vc.data.CoreTACProgram
import vc.data.TACExpr
import vc.data.TACSymbol
import vc.data.asTACExpr
import verifier.splits.IntervalsRepresentativePicker.pickRepresentatives
import verifier.splits.SplitAddress.Assumption.AddedAssumption

/**
 * Splits by adding a [SplitAddress.Assumption], constraining a variable to a few constant values. Clearly meaning that
 * in most cases, it's an under-approximation.
 */
abstract class VarSamplerSplitter(val node: SplitTree.Node, val alreadySplitUpon: MutableSet<TACSymbol.Var>) :
    Splitter {

    data class SplitVar(val ptr: CmdPointer, val v: TACSymbol.Var, val s: Intervals)

    abstract fun bestSplitVar(actualTAC: CoreTACProgram): SplitVar?

    private var splitVar: SplitVar? by InitOnceProperty()

    override fun splittable(actualTAC: CoreTACProgram): Boolean {
        splitVar = bestSplitVar(actualTAC)
        return splitVar != null
    }

    private fun restrictToReps(actualTAC: CoreTACProgram, howMany: Int): List<SplitAddress> =
        with(splitVar!!) {
            pickRepresentatives(s, howMany).mapIndexed { i, rep ->
                SplitAddress.Assumption(
                    node.address,
                    AddedAssumption(
                        actualTAC,
                        ptr,
                        TACExpr.BinRel.Eq(v.asSym(), rep.asTACExpr(v.tag)),
                        isUnderApprox = s.numElements > howMany.asExtBig
                    ),
                    i
                )
            }
        }

    override fun split(actualTAC: CoreTACProgram): List<SplitTree.Node> {
        require(splitVar != null) {
            "Splitting before checking for splittability or without being splittable."
        }
        alreadySplitUpon += splitVar!!.v
        return node.setChildren(
            restrictToReps(actualTAC, 3).map { it to SizeSideScore(0) }
        )
    }

}
