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

/**
 * Qualifier recording that the variable holds the veracity of the predicate [op1] [condition] [op2].
 * In other words, if we have `R1 < R2` attached to a variable R3, and we know that R3 is 0, then
 * !(R1 < R2) is true.
 */
interface ConditionQualifier {
    enum class Condition(val isSigned: Boolean, val isEquality: Boolean) {
        EQ(false, true),
        NEQ(false, true),
        LT(false, false),
        LE(false, false),
        SLT(true, false),
        SLE(true, false);

        /**
         * given o1 [Condition] op2, returns the [Condition] that applied to SWAPPED operands yields
         * the negation of the original condition, i.e. `!(a op b) <=> (b op.flip() a)`
         */
        fun flip() : Condition {
            return when(this) {
                EQ -> NEQ
                NEQ -> EQ
                LT -> LE
                LE -> LT
                SLT -> SLE
                SLE -> SLT
            }
        }
    }

    companion object {
        fun <T: ConditionQualifier> flip(x: T, mk: (TACSymbol, TACSymbol, Condition) -> T) : T {
            return mk(x.op2, x.op1, x.condition.flip())
        }
    }

    val condition: Condition
    val op1: TACSymbol
    val op2: TACSymbol
}

interface LogicalConnectiveQualifier {
    enum class LBinOp {
        OR,
        AND;

        fun flip() : LBinOp {
            return when(this) {
                OR -> AND
                AND -> OR
            }
        }
    }

    companion object {
        fun <T: LogicalConnectiveQualifier> flip(x: T, mk: (TACSymbol.Var, TACSymbol.Var, LBinOp, Boolean) -> T) : T {
            return mk(
                x.op1,
                x.op2,
                x.connective.flip(),
                !x.applyNot
            )
        }
    }

    val applyNot: Boolean
    val op1: TACSymbol.Var
    val op2: TACSymbol.Var
    val connective: LBinOp
}
