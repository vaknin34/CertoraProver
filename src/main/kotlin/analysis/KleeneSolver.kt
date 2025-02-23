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

package analysis

/**
 * Solver for monotone, upper-continuous functions over maps from [K] to values of type [V] that form
 * a join lattice as described by [lattice].
 */
class KleeneSolver<K, V: Any>(private val lattice: JoinLattice<V>) {
    /**
     * An equation over maps of [K] to [V]. The equation must assume
     * that an unmapped key is the implicit least element of [V] (i.e., bottom)
     */
    interface SolverFunction<K, V> {
        fun eval(st: Map<K, V>) : V?
    }

    /**
     * Find a fixpoint for series of equations as specified in [eqn]. Iterates from the bottom element
     * of Map<K, V>, i.e., all keys map to null, the implicit bottom element of [V].
     *
     * Once the solution stabilizes, we must have a fixpoint of [eqn], per kleene's fixpoint theorem.
     */
    fun <T: SolverFunction<K, V>> solve(eqn: Map<K, T>): Map<K, V> {
        var changed = true
        val state = mutableMapOf<K, V>()
        val mut = mutableMapOf<K, V>()
        while(changed) {
            changed = false
            for((which, f) in eqn) {
                val res = f.eval(state)
                if(res == null) {
                    if(state[which] != null) {
                        throw IllegalStateException("Non-monotonic result for $which")
                    }
                } else {
                    if(which !in state) {
                        mut[which] = res
                    } else {
                        val old = state[which]!!
                        val new = lattice.join(old, res)
                        if(!lattice.equiv(new, old)) {
                            mut[which] = new
                        }
                    }
                }
            }

            if(mut.isNotEmpty()) {
                state.putAll(mut)
                mut.clear()
                changed = true
            }
        }
        return state
    }
}