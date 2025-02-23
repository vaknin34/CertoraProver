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

import analysis.LTACCmd
import analysis.opt.intervals.Intervals
import analysis.opt.intervals.IntervalsCalculator
import report.dumps.CountDifficultOps
import utils.*
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACSymbol
import vc.data.tacexprutil.unquantifiedSubs
import verifier.DeciderCalculator

/**
 * The split variable is chosen from the parameters of non-linear operation with the minimal [Intervals].
 * It's not necessarily the parameter itself that is chosen, but possibly one that decides it (see [DeciderCalculator])
 */
class NonLinearSplitter(node: SplitTree.Node, alreadySplitUpon: MutableSet<TACSymbol.Var>) :
    VarSamplerSplitter(node, alreadySplitUpon) {

    override fun bestSplitVar(actualTAC: CoreTACProgram) =
        Worker(actualTAC).bestSplitVar()

    private inner class Worker(private val actualTAC: CoreTACProgram) {
        private val g = actualTAC.analysisCache.graph
        private val intervals by lazy {
            IntervalsCalculator(actualTAC, preserve = { false })
        }
        private val decider by lazy {
            DeciderCalculator(actualTAC).apply { go() }
        }

        private var bestSplit: SplitVar? = null

        private fun analyse(lcmd: LTACCmd) {
            val (ptr, cmd) = lcmd
            if (cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
                return
            }
            for (exp in cmd.rhs.unquantifiedSubs) {
                CountDifficultOps
                    .processExpFlat(exp, null)
                    .mapNotNull { nonLinearArg ->
                        // consider all variables that "decide" this argument, and among them, return the one
                        // that has the minimal range.
                        decider.rhsVal(ptr, nonLinearArg).setOrNull
                            ?.takeIf { it.isNotEmpty() }
                            ?.minBy { intervals.getS(it.ptr, it.v).numElements }
                    }
                    .forEach { (p, v) ->
                        val s = intervals.getS(p, v)
                        if (s.isConst) {
                            return@forEach
                        }

                        if (bestSplit == null ||
                            (bestSplit!!.v in alreadySplitUpon && v !in alreadySplitUpon) ||
                            (s.numElements < bestSplit!!.s.numElements && bestSplit!!.v in alreadySplitUpon == v in alreadySplitUpon)
                        ) {
                            bestSplit = SplitVar(p, v, s)
                        }
                    }
            }
        }


        fun bestSplitVar(): SplitVar? {
            for (b in actualTAC.topoSortFw) {
                g.elab(b).commands.forEach(::analyse)
            }
            return bestSplit
        }
    }

}
