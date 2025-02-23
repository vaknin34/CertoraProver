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

import evm.EVM_BITWIDTH256
import evm.MAX_EVM_INT256
import smtlibutils.data.*
import utils.*
import java.math.BigInteger

object SmtExpIntTermBuilder : AbstractSmtExpTermBuilder() {
    override val numericType: Sort
        get() = Sort.IntSort

    override fun const(x: BigInteger): SmtExp = script.number(x)

    override fun plus(ops: List<SmtExp>): SmtExp = script.apply(SmtIntpFunctionSymbol.IRA.Add(), ops)

    override fun mult(ops: List<SmtExp>): SmtExp = script.apply(SmtIntpFunctionSymbol.IRA.Mul(), ops)

    override fun minus(op1: SmtExp, op2: SmtExp): SmtExp = script.apply(SmtIntpFunctionSymbol.IRA.Sub(), op1, op2)

    override fun div(op1: SmtExp, op2: SmtExp): SmtExp = script.apply(SmtIntpFunctionSymbol.Ints.Div, op1, op2)

    override fun bwAnd(op1: SmtExp, op2: SmtExp): SmtExp? = null

    override fun bwOr(op1: SmtExp, op2: SmtExp): SmtExp? = null

    override fun shl(op1: SmtExp, op2: SmtExp): SmtExp? =
        op2.asBigIntOrNull()?.toIntOrNull()?.takeIf { it < EVM_BITWIDTH256 }?.let { shift ->
            script.apply(SmtIntpFunctionSymbol.IRA.Mul(), op1, const(BigInteger.ONE.shl(shift)))
        }

    override fun shr(op1: SmtExp, op2: SmtExp): SmtExp? = null

    override fun bwNot(op: SmtExp): SmtExp? = null

    override fun gt(op1: SmtExp, op2: SmtExp): SmtExp = script.apply(SmtIntpFunctionSymbol.IRA.Gt(), op1, op2)

    override fun lt(op1: SmtExp, op2: SmtExp): SmtExp = script.apply(SmtIntpFunctionSymbol.IRA.Lt(), op1, op2)

    override fun le(op1: SmtExp, op2: SmtExp): SmtExp = script.apply(SmtIntpFunctionSymbol.IRA.Le(), op1, op2)

    override fun ge(op1: SmtExp, op2: SmtExp): SmtExp = script.apply(SmtIntpFunctionSymbol.IRA.Ge(), op1, op2)

    /**
     * Returns SMT expression for checking if [e] is a positive signed int, i.e.
     * SMT expression for "e <= 2^255 - 1 (MAX_EVM_INT256)".
     *
     * @param e: SMT expression
     * @return SMT expression for "e <= 2^255 - 1"
     */
    private fun isPositiveSignedInt(e: SmtExp): SmtExp =
            script.apply(
                    SmtIntpFunctionSymbol.IRA.Le(),
                    e,
                    const(MAX_EVM_INT256)
            )


    override fun slt(op1: SmtExp, op2: SmtExp): SmtExp =
        script.or(
                script.and(
                        // op1 is negative & op2 is positive
                        script.not(isPositiveSignedInt(op1)), isPositiveSignedInt(op2)
                ),
                script.and(
                        // both are of same sign
                        script.eq(isPositiveSignedInt(op1), isPositiveSignedInt(op2)),

                        // op1 < op2
                        script.apply(
                                SmtIntpFunctionSymbol.IRA.Lt(),
                                op1,
                                op2
                        )
                )
        )

    override fun sgt(op1: SmtExp, op2: SmtExp): SmtExp =
            script.or(
                    script.and(
                            // op1 is positive & op2 is negative
                            isPositiveSignedInt(op1), script.not(isPositiveSignedInt(op2))
                    ),
                    script.and(
                            // both are of same sign
                            script.eq(isPositiveSignedInt(op1), isPositiveSignedInt(op2)),

                            // op1 > op2
                            script.apply(
                                    SmtIntpFunctionSymbol.IRA.Gt(),
                                    op1,
                                    op2
                            )
                    )
            )

    override fun sle(op1: SmtExp, op2: SmtExp): SmtExp =
            script.or(
                    script.and(
                            // op1 is negative & op2 is positive
                            script.not(isPositiveSignedInt(op1)), isPositiveSignedInt(op2)
                    ),
                    script.and(
                            // both are of same sign
                            script.eq(isPositiveSignedInt(op1), isPositiveSignedInt(op2)),

                            // op1 <= op2
                            script.apply(
                                    SmtIntpFunctionSymbol.IRA.Le(),
                                    op1,
                                    op2
                            )
                    )
            )

    override fun sge(op1: SmtExp, op2: SmtExp): SmtExp =
            script.or(
                    script.and(
                            // op1 is positive & op2 is negative
                            isPositiveSignedInt(op1), script.not(isPositiveSignedInt(op2))
                    ),
                    script.and(
                            // both are of same sign
                            script.eq(isPositiveSignedInt(op1), isPositiveSignedInt(op2)),

                            // op1 >= op2
                            script.apply(
                                    SmtIntpFunctionSymbol.IRA.Ge(),
                                    op1,
                                    op2
                            )
                    )
            )

    override fun fork(): AbstractSmtExpTermBuilder = this
}
