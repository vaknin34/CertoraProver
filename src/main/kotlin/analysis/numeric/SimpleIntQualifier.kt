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

import vc.data.TACSymbol
import java.math.BigInteger

sealed class SimpleIntQualifier : SelfQualifier<SimpleIntQualifier> {
    abstract fun flip(): SimpleIntQualifier?

    data class Condition(
        override val op1: TACSymbol,
        override val op2: TACSymbol,
        override val condition: ConditionQualifier.Condition
    ) : SimpleIntQualifier(), ConditionQualifier {
        override fun relates(v: TACSymbol.Var): Boolean = op1 == v || op2 == v
        override fun hashCode(): Int {
            return utils.hashObject(this)
        }

        override fun saturateWith(equivClasses: VariableSaturation): List<SimpleIntQualifier> {
            return equivClasses(op1).flatMap { x ->
                equivClasses(op2).map {y ->
                    Condition(x, y, condition)
                }
            }
        }

        override fun flip() = ConditionQualifier.flip(this, ::Condition)
    }

    data class LogicalConnective(
        override val op1: TACSymbol.Var,
        override val op2: TACSymbol.Var,
        override val connective: LogicalConnectiveQualifier.LBinOp,
        override val applyNot: Boolean
    ) : SimpleIntQualifier(), LogicalConnectiveQualifier {
        constructor(connective: LogicalConnectiveQualifier.LBinOp, op1: TACSymbol.Var, op2: TACSymbol.Var) : this(
            op1, op2, connective, false
        )

        override fun flip(): SimpleIntQualifier? {
            return LogicalConnectiveQualifier.flip(this, ::LogicalConnective)
        }

        override fun relates(v: TACSymbol.Var): Boolean {
            return v == op1 || v == op2
        }

        override fun hashCode(): Int {
            return utils.hashObject(this)
        }

        override fun saturateWith(equivClasses: VariableSaturation): List<SimpleIntQualifier> {
            return equivClasses(op1).flatMap { x ->
                equivClasses(op2).map { y ->
                    LogicalConnective(x, y, connective, applyNot)
                }
            }
        }
    }

    data class MultipleOf(val factor: BigInteger) : SimpleIntQualifier() {
        init {
            check(factor > BigInteger.ZERO)
            { "Factor is $factor, should be >0" }
        }
        override fun relates(v: TACSymbol.Var): Boolean = false

        override fun saturateWith(equivClasses: VariableSaturation): List<MultipleOf> =
            datastructures.stdcollections.listOf(this)

        override fun flip(): SimpleIntQualifier? = null
    }

    /** if x: ModularUpperBound(y, m, b):
     *  then (x < y if b else x <= y) AND (m divides y - x)
     */
    data class ModularUpperBound(
        override val other: TACSymbol,
        override val modulus: BigInteger,
        override val strong: Boolean
    ): SimpleIntQualifier(), ModularUpperBoundQualifier {
        init {
            check(modulus > BigInteger.ZERO)
            { "Modulus is $modulus, should be >0" }
        }

        override fun relates(v: TACSymbol.Var): Boolean {
            return other == v
        }

        override fun saturateWith(equivClasses: VariableSaturation): List<SimpleIntQualifier> {
            return equivClasses(other).map {
                ModularUpperBound(it, this.modulus, this.strong)
            }
        }


        override fun flip(): SimpleIntQualifier? = null
    }
}
