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

import analysis.LTACCmd
import analysis.LTACCmdView
import com.certora.collect.*
import vc.data.TACCmd
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * Expression semantics that operate over the [IntValue] domain with
 * a simple map from variables to [IntValue] as the state abstraction.
 */
open class SimpleIntervalExpressionSemantics<in W>(
        override val valueSemantics: IValueSemantics<Map<TACSymbol.Var, IntValue>, IntValue, W>
) : NonRelationalExpressionInterpreter<TreapMap<TACSymbol.Var, IntValue>, IntValue, W>() {
    override val nondet: IntValue
        get() = IntValue.Nondet

    override fun assign(toStep: TreapMap<TACSymbol.Var, IntValue>, lhs: TACSymbol.Var, newValue: IntValue, input: TreapMap<TACSymbol.Var, IntValue>, whole: W, wrapped: LTACCmd): TreapMap<TACSymbol.Var, IntValue> {
        return toStep + (lhs to newValue)
    }

    override fun interp(o1: TACSymbol, toStep: TreapMap<TACSymbol.Var, IntValue>, input: TreapMap<TACSymbol.Var, IntValue>, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): IntValue {
        return when(o1) {
            is TACSymbol.Const -> this.liftConstant(o1.value)
            is TACSymbol.Var -> input[o1] ?: nondet
        }
    }

    override fun liftConstant(value: BigInteger): IntValue {
        return IntValue.Constant(value)
    }

}
