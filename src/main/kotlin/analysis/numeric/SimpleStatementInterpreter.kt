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

import analysis.LTACCmdView
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol

/**
 * A basic Statement interpreter that delegates all expression interpretation to [expressionSemantics]
 */
abstract class SimpleStatementInterpreter<S, in W>(
        private val expressionSemantics: IExpressionInterpreter<S, W>
) : AbstractStatementInterpreter<S, W>() {
    override fun stepExpression(lhs: TACSymbol.Var, rhs: TACExpr, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        return expressionSemantics.stepExpression(lhs, rhs, toStep, input, whole, l)
    }
}