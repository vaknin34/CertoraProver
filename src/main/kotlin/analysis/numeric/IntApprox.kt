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

package analysis.numeric

import java.math.BigInteger

interface IntApprox<T>: LatticeElem<T, T> {
    fun getUpperBound(): BigInteger?
    fun getLowerBound(): BigInteger?

    fun mult(other: T) : Pair<T, Boolean>
    fun add(other: T) : Pair<T, Boolean>
    fun sub(other: T) : Pair<T, Boolean>

    fun shiftLeft(lb: BigInteger, ub: BigInteger) : T

    fun mayOverlap(other: T) : Boolean

    val isConstant : Boolean
    val c : BigInteger

    fun mayEqual(c: BigInteger): Boolean {
        val lb = getLowerBound()
        val ub = getUpperBound()
        if(ub != null) {
            if(ub < c) {
                return false
            }
        }
        return !(lb != null && lb > c)
    }

    fun mustNotEqual(c: BigInteger) = !mayEqual(c)

    fun mustEqual(c: BigInteger): Boolean {
        val lb = getLowerBound()
        return lb == getUpperBound() && lb == c
    }

    fun shiftRight(lb: BigInteger, ub: BigInteger) : T
}
