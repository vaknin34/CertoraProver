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

package vc.data.state

import com.certora.collect.*
import datastructures.stdcollections.*
import solver.CounterexampleModel
import vc.data.TACSymbol

/**
 * Base state class
 */
interface TACState {

    /**
     * @param [v] the var to get/store
     * This is for initializing havoc variables at the first time they are needed while not changing non-havoc variables.
     */
    operator fun get(v: TACSymbol.Var): TACValue?
    fun storeVar(v: TACSymbol.Var, value: TACValue): TACState
}

/** "top" element in the lattice of states. It is forbidden (will crash) to store into this, to its use is when we
 * want an empty state that can never be updated. */
object EmptyTACState : TACState {
    override fun get(v: TACSymbol.Var): TACValue = TACValue.Uninitialized
    override fun storeVar(v: TACSymbol.Var, value: TACValue): TACState {
        throw UnsupportedOperationException("Cannot store in an empty state.")
    }
}

class SimpleTACState(private val assignment: TreapMap<TACSymbol.Var, TACValue>): TACState {
    override fun get(v: TACSymbol.Var): TACValue? = assignment[v]

    override fun storeVar(v: TACSymbol.Var, value: TACValue): SimpleTACState =
        SimpleTACState(assignment + (v to value))
}

val CounterexampleModel.asSimpleTACState get() = SimpleTACState(this.tacAssignments.toTreapMap())
