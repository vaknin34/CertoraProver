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
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol

/**
 * A basic implementation of an abstract interpreter, which uses [TrivialPathSemantics] for paths,
 * and [expressionInterpreter] to interpret assignments with [TACExpr] right hand sides.
 *
 * All other statements are modeled with havoc, as implemented by [forget]
 */
abstract class SimpleAbstractInterpreter<S, in W : Any>(
        protected val expressionInterpreter: IExpressionInterpreter<S, W>
) : AbstractAbstractInterpreter<W, S>() {
    /**
     * Havoc (aka forget) the value of [lhs] in the state [toStep]
     */
    abstract fun forget(lhs: TACSymbol.Var, toStep: S) : S

    override val pathSemantics: IPathSemantics<S, W> = TrivialPathSemantics()
    override val statementInterpreter: IStatementInterpreter<S, W> = object : AbstractStatementInterpreter<S, W>() {
        override fun forget(lhs: TACSymbol.Var, toStep: S, input: S, whole: W, l: LTACCmd): S {
            return this@SimpleAbstractInterpreter.forget(lhs, toStep)
        }

        override fun stepExpression(lhs: TACSymbol.Var, rhs: TACExpr, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
            return expressionInterpreter.stepExpression(lhs, rhs, toStep, input, whole, l)
        }
    }

    override fun killLHS(
        lhs: TACSymbol.Var,
        s: S,
        w: W,
        narrow: LTACCmdView<TACCmd.Simple.AssigningCmd>
    ): S {
        return s
    }

    override fun postStep(stepped: S, l: LTACCmd): S {
        return stepped
    }
}
