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

package analysis.opt.numeric

import analysis.numeric.OpenInterval
import analysis.opt.numeric.VROInt.Companion.nondetOf
import analysis.worklist.SimpleWorklist
import com.certora.collect.*
import datastructures.stdcollections.*
import tac.Tag
import utils.keysMatching
import vc.data.TACSymbol

/**
 * Interpret the symbol [op] in the state `this`, assuming that unmapped variables have the
 * value [VROInt.nondet256], [VROInt.nondetFull] or [VROInt.nondetBool]
 */
fun Map<TACSymbol.Var, VROInt>.interp(op: TACSymbol) : VROInt {
    return when(op) {
        is TACSymbol.Const -> VROInt(OpenInterval(op.value), treapSetOf())
        is TACSymbol.Var -> this[op] ?: op.tag.nondetOf()
    }
}

/**
 * Find the equivalence class of [sym]. If it is a constant k, simple return that k (NB, we could search for all
 * variables with constant value k, but we don't).
 *
 * Otherwise, iteratively expand the equivalence class by looking for variables
 * which are known (via [analysis.opt.numeric.VROQuals.MustEqual] qualifiers) to be equal
 * to sym, and then for variables known to be equal to those, and so on.
 */
fun Map<TACSymbol.Var, VROInt>.saturate(sym: TACSymbol) : Collection<TACSymbol> {
    if(sym !is TACSymbol.Var) {
        return listOf(sym)
    }
    val currState = this
    val output = mutableSetOf<TACSymbol.Var>()
    val visited = mutableSetOf<TACSymbol.Var>()
    SimpleWorklist.iterateWorklist(listOf(sym)) { cand, nxt ->
        if(!visited.add(cand)) {
            return@iterateWorklist
        }
        if(cand.tag == Tag.Bit256) {
            output.add(cand)
        }
        nxt.addAll(currState.keysMatching { _, vroInt ->
            vroInt.qual.any {
                it is VROQuals.MustEqual && it.other == cand
            }
        })
        currState[sym]?.qual?.forEach {
            if(it is VROQuals.MustEqual) {
                nxt.add(it.other)
            }
        }
    }
    return output
}
