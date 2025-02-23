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

import analysis.opt.intervals.IntervalsCalculator
import tac.Tag
import utils.*
import vc.data.CoreTACProgram
import vc.data.TACKeyword
import vc.data.TACSymbol
import vc.data.TACSymbol.Var.Companion.KEYWORD_ENTRY
import verifier.DeciderCalculator

/**
 * Chooses a variables that "decides" the most variables, [DeciderCalculator].
 */
class DeciderSplitter(node: SplitTree.Node, alreadySplitUpon: MutableSet<TACSymbol.Var>) :
    VarSamplerSplitter(node, alreadySplitUpon) {

    override fun bestSplitVar(actualTAC: CoreTACProgram) =
        Worker(actualTAC).bestSplitVar()

    private inner class Worker(private val actualTAC: CoreTACProgram) {
        private val g = actualTAC.analysisCache.graph
        private val intervals = IntervalsCalculator(actualTAC, preserve = { false })
        private val decider = DeciderCalculator(actualTAC).apply { go() }

        fun bestSplitVar(): SplitVar? {
            var bestSplit: SplitVar? = null
            var bestScore = -1
            for (b in actualTAC.topoSortFw) {
                g.elab(b).commands
                    .mapNotNull { (ptr, cmd) -> ptr `to?` cmd.getLhs() }
                    .forEach { (ptr, lhs) ->
                        when(lhs.tag) {
                            Tag.Int, Tag.Bit256, Tag.Bool -> Unit
                            else -> return@forEach
                        }
                        if (lhs.meta[KEYWORD_ENTRY]?.name == TACKeyword.MEM64.getName()) {
                            return@forEach
                        }
                        val s = intervals.getLhs(ptr)
                        if (s.isConst) {
                            return@forEach
                        }
                        val score = decider.lhsVal(ptr)?.setOrNull?.size ?: -1
                        if (score > bestScore) {
                            bestScore = score
                            bestSplit = SplitVar(ptr, lhs, s)
                        }
                    }
            }

            return bestSplit
        }
    }

}

