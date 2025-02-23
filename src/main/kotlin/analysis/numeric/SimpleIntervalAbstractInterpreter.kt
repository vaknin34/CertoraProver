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

import com.certora.collect.*
import vc.data.TACSymbol

/**
 * An abstract interpreter which operates over a state abstract that maps
 * variables to [IntValue] instances.
 */
abstract class SimpleIntervalAbstractInterpreter<in W : Any>(
        expressionInterpreter: IExpressionInterpreter<TreapMap<TACSymbol.Var, IntValue>, W>
) : SimpleAbstractInterpreter<TreapMap<TACSymbol.Var, IntValue>, W>(expressionInterpreter) {
    override fun forget(lhs: TACSymbol.Var, toStep: TreapMap<TACSymbol.Var, IntValue>): TreapMap<TACSymbol.Var, IntValue> =
        toStep + (lhs to IntValue.Nondet)
}
