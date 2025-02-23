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

import evm.MAX_EVM_UINT256
import smtlibutils.data.*
import java.math.BigInteger

class InvalidBitVectorTerm(override val message: String?): Exception(message)

object SmtExpBitVectorTermBuilder : AbstractSmtExpTermBuilder() {
    override val numericType: Sort
        get() = Sort.BV256Sort

    override fun const(x: BigInteger): SmtExp {
        if (x < BigInteger.ZERO) {
            throw InvalidBitVectorTerm("trying to create a negative bv256 constant $x")
        }
        if (x > MAX_EVM_UINT256) {
            throw InvalidBitVectorTerm("trying to create an overly large bv256 constant $x")
        }
        return script.bitvector(x, 256)
    }

    override fun plus(ops: List<SmtExp>): SmtExp = ops.reduce { a, b ->
        script.apply(SmtIntpFunctionSymbol.BV.BinOp.BvAdd(256), a, b)
    }

    override fun mult(ops: List<SmtExp>): SmtExp = ops.reduce { a, b ->
        script.apply(SmtIntpFunctionSymbol.BV.BinOp.BvMul(256), a, b)
    }

    override fun minus(op1: SmtExp, op2: SmtExp): SmtExp = script.apply(
        SmtIntpFunctionSymbol.BV.BinOp.BvSub(256),
        op1,
        op2
    )

    override fun div(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.BinOp.BvUDiv(256), op1, op2)

    override fun bwAnd(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.BinOp.BvAnd(256), op1, op2)

    override fun bwOr(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.BinOp.BvOr(256), op1, op2)

    override fun shl(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.BinOp.BvShL(256), op1, op2)

    override fun shr(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.BinOp.BvLShr(256), op1, op2)

    override fun bwNot(op: SmtExp): SmtExp? =
        script.apply(SmtIntpFunctionSymbol.BV.Un.BvNot(256), op)

    override fun gt(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.Rel.BvUGt(256), op1, op2)

    override fun lt(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.Rel.BvULt(256), op1, op2)

    override fun le(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.Rel.BvULe(256), op1, op2)

    override fun ge(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.Rel.BvUGe(256), op1, op2)

    override fun sgt(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.Rel.BvSGt(256), op1, op2)

    override fun slt(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.Rel.BvSLt(256), op1, op2)

    override fun sle(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.Rel.BvSLe(256), op1, op2)

    override fun sge(op1: SmtExp, op2: SmtExp): SmtExp =
        script.apply(SmtIntpFunctionSymbol.BV.Rel.BvSGe(256), op1, op2)

    override fun fork(): AbstractSmtExpTermBuilder  = this

}