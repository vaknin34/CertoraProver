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

package analysis.alloc

import analysis.*
import utils.*
import vc.data.TACCmd
import vc.data.TACSymbol

class StorageArrayLengthFinder(private val graph: TACCommandGraph) {
    private val nonTrivialDefAnalysis by lazy {
        NonTrivialDefAnalysis(graph)
    }

    private val mustBeConstantAnalysis by lazy {
        MustBeConstantAnalysis(graph, nonTrivialDefAnalysis)
    }

    fun isStorageArrayLengthRead(where: LTACCmdView<TACCmd.Simple.AssigningCmd.WordLoad>, dynBlock: AllocationAnalysis.Alloc.DynamicBlock) : Boolean {
        if(where.ptr.block != dynBlock.elemSym.first.block || where.ptr.pos < dynBlock.elemSym.first.pos) {
            return false
        }
        val def = nonTrivialDefAnalysis.nontrivialDefSingleOrNull(dynBlock.elemSym.second, dynBlock.elemSym.first) ?: return false
        // preceding read in this block
        if (def.block != dynBlock.elemSym.first.block || def.pos >= dynBlock.elemSym.first.pos) {
            return false
        }
        val lc = graph.elab(def)
        if (lc.cmd !is TACCmd.Simple.AssigningCmd.WordLoad) {
            return false
        }
        val readIdx = lc.cmd.loc
        val constIdx = this.mustBeConstantAnalysis.mustBeConstantAt(def, readIdx)

        if(graph.iterateBlock(def).any {
                    it.ptr.pos < where.ptr.pos && it.cmd is TACCmd.Simple.WordStore
                }) {
            return false
        }
        if(constIdx != null) {
            return this.mustBeConstantAnalysis.mustBeConstantAt(where.ptr, where.cmd.loc) == constIdx
        }
        check(readIdx is TACSymbol.Var)
        if(where.cmd.loc !is TACSymbol.Var) {
            return false
        }
        return where.cmd.loc in graph.cache.gvn.findCopiesAt(where.ptr, def to readIdx)
    }
}
