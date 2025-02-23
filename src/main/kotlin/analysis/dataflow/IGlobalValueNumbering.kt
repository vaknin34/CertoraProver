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

package analysis.dataflow

import analysis.CmdPointer
import datastructures.stdcollections.*
import vc.data.TACSymbol

/**
 * GlobalValueNumbering interface: if two expressions have the same value number
 * (in the same graph) then they must be equal.
 */
interface IGlobalValueNumbering: IMustEqualsAnalysis {

    /**
     * Return the set of variables whose value at [target] is equal to the value of [source].second
     * at [source].first
     */
    fun findCopiesAt(target: CmdPointer, source: Pair<CmdPointer, TACSymbol.Var>): Set<TACSymbol.Var>

    companion object {
        @JvmName("findCopiesSymbol")
        fun IGlobalValueNumbering.findCopiesAt(target: CmdPointer, source: Pair<CmdPointer, TACSymbol>) : Set<TACSymbol> {
            if(source.second is TACSymbol.Const) {
                return setOf(source.second)
            } else {
                return findCopiesAt(target, source.first to (source.second as TACSymbol.Var))
            }
        }
    }
}
