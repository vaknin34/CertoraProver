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

package instrumentation.transformers

import analysis.NonTrivialDefAnalysis
import analysis.maybeNarrow
import utils.mapNotNull
import vc.data.CoreTACProgram
import vc.data.SimplePatchingProgram.Companion.patchForEach
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACKeyword
import datastructures.stdcollections.*

/**
 * Recognizes patterns like:
 * ```
 * if(*) {
 *    z = fp
 *    y = z
 * } else {
 *    w = fp
 *    y = w
 * }
 * fp = y
 * ```
 *
 * This happens in via-ir for some godforsaken reason.
 */
object RedundantFreePointerNormalizer {
    fun rewrite(p: CoreTACProgram) : CoreTACProgram {
        val nontriv = NonTrivialDefAnalysis(p.analysisCache.graph)
        val graph = p.analysisCache.graph
        return p.parallelLtacStream().mapNotNull {
            val lc = it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>() ?: return@mapNotNull null
            if(lc.cmd.lhs != TACKeyword.MEM64.toVar()) {
                return@mapNotNull null
            }
            val rhs = (lc.cmd.rhs as? TACExpr.Sym.Var)?.s ?: return@mapNotNull null
            val defs = nontriv.nontrivialDef(rhs, lc.ptr, TACKeyword.MEM64.toVar())
            val gvn = p.analysisCache.gvn
            if(!defs.all {
                val other = graph.elab(it).maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.cmd?.rhs?.getAs<TACExpr.Sym.Var>()?.s ?: return@all false
                other in gvn.findCopiesAt(it, lc.ptr to lc.cmd.lhs)
            }) {
                return@mapNotNull null
            }
            it
        }.patchForEach(p, check = true) {
            replaceCommand(it.ptr, listOf(TACCmd.Simple.NopCmd))
        }
    }
}
