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

package analysis.smtblaster

import java.math.BigInteger

interface ISMTTermBuilder<SortType, ReprType> {
    val numericType: SortType

    fun const(x: BigInteger) : ReprType
    fun const(x: Int) = const(x.toBigInteger())

    /** override this at your own peril -- I ran into ClassCastExceptions (varargs vs variance of arrays vs generics) */
    // ^ ^ yes you would encounter those!
    fun plus(vararg ops: ReprType) : ReprType = plus(ops.toList())
    fun plus(ops: List<ReprType>) : ReprType

    /** override this at your own peril -- I ran into ClassCastExceptions (varargs vs variance of arrays vs generics) */
    fun mult(vararg ops: ReprType) : ReprType = mult(ops.toList())
    fun mult(ops: List<ReprType>) : ReprType

    fun minus(op1: ReprType, op2: ReprType) : ReprType
    fun div(op1: ReprType, op2: ReprType) : ReprType

    // optional bitwise operations
    fun bwAnd(op1: ReprType, op2: ReprType) : ReprType?
    fun bwOr(op1: ReprType, op2: ReprType) : ReprType?
    fun shl(op1: ReprType, op2: ReprType) : ReprType?
    fun shr(op1: ReprType, op2: ReprType) : ReprType?
    fun bwNot(op: ReprType) : ReprType?

    // relation operations
    fun gt(op1: ReprType, op2: ReprType) : ReprType
    fun lt(op1: ReprType, op2: ReprType) : ReprType
    fun eq(op1: ReprType, op2: ReprType) : ReprType
    fun le(op1: ReprType, op2: ReprType) : ReprType
    fun ge(op1: ReprType, op2: ReprType) : ReprType

    // signed relation operators
    fun sgt(op1: ReprType, op2: ReprType) : ReprType
    fun slt(op1: ReprType, op2: ReprType) : ReprType
    fun sle(op1: ReprType, op2: ReprType) : ReprType
    fun sge(op1: ReprType, op2: ReprType) : ReprType

    fun toIdent(string: String) : ReprType

    fun land(vararg ops: ReprType) : ReprType = land(ops.toList())
    fun land(ops: List<ReprType>) : ReprType

    fun lor(vararg ops: ReprType) : ReprType = lor(ops.toList())
    fun lor(op: List<ReprType>) : ReprType

    fun lnot(op: ReprType) : ReprType

    fun ite(cond: ReprType, trBranch: ReprType, falseBranch: ReprType) : ReprType
    fun apply(f: String, ops: List<ReprType>) : ReprType
}

