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

package sbf.domains

import sbf.cfg.CondOp

/**
 *  An interface to represent an approximation of a numerical value (aka basis)
 *  Possible implementations are constants, intervals, congruences, etc.
 **/

interface NumValue<V> {
    // Return null if the numerical value cannot be expressed as a signed long
    fun get(): Long?

    /* Numerical operations */
    fun add(other: V): V
    fun add(n: Long): V
    fun sub(other: V): V
    fun sub(n: Long): V
    fun mul(other: V): V
    fun mul(n: Long): V
    fun and(other: V): V
    fun or(other: V): V
    fun xor(other: V): V
    fun udiv(other: V): V
    fun sdiv(other: V): V
    fun urem(other: V): V
    fun srem(other: V): V
    fun arsh(other: V): V
    fun rsh(other: V): V
    fun lsh(other: V): V
    fun assume(op: CondOp, other: V): TriBoolean
    /* lattice operations */
    fun isTop(): Boolean
    fun isBottom(): Boolean
    fun join(other: V): V
    fun meet(other: V): V
    fun lessOrEqual(other: V): Boolean
    override fun toString(): String
}
