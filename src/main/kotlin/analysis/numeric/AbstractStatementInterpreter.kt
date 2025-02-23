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
import analysis.narrow
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol

/**
 * An abstract starting point for implementing a statement interpreter.
 *
 * This statement interpreter provides "hooks" for interpreting:
 * + Expressions ([stepExpression]
 * + Memory reads ([stepReadMemory])
 * + Word loads ([stepReadStorage])
 *
 * Other statement forms are modeled imprecisely with the [forget] functions.
 *
 * As usual, [S] represents the target state of this particular interpreter, which may
 * be embedded within some larger set of states [W]
 */
abstract class AbstractStatementInterpreter<S, in W> : IStatementInterpreter<S, W> {
    override fun stepCommand(l: LTACCmd, toStep: S, input: S, whole: W): S {
        if(l.cmd !is TACCmd.Simple.AssigningCmd) {
            return toStep
        }
        return when(l.cmd) {
            is TACCmd.Simple.AssigningCmd.AssignExpCmd -> {
                this.stepExpression(l.cmd.lhs, l.cmd.rhs, toStep, input, whole, l.narrow())
            }
            is TACCmd.Simple.AssigningCmd.AssignSha3Cmd,
            is TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd -> {
                this.forget(l.cmd.lhs, toStep, input, whole, l)
            }
            is TACCmd.Simple.AssigningCmd.ByteLoad -> {
                this.stepReadMemory(l.cmd.lhs, l.cmd.loc, l.cmd.base, toStep, input, whole, l)
            }
            is TACCmd.Simple.AssigningCmd.ByteStore,
            is TACCmd.Simple.AssigningCmd.ByteStoreSingle -> {
                toStep
            }
            is TACCmd.Simple.AssigningCmd.WordLoad -> {
                this.stepReadStorage(l.cmd.lhs, l.cmd.loc, l.cmd.base, toStep, input, whole, l)
            }
            is TACCmd.Simple.AssigningCmd.AssignMsizeCmd,
            is TACCmd.Simple.AssigningCmd.AssignGasCmd,
            is TACCmd.Simple.AssigningCmd.AssignHavocCmd -> {
                this.forget(l.cmd.lhs, toStep, input, whole, l)
            }
        }
    }

    open fun stepReadStorage(
            lhs: TACSymbol.Var,
            loc: TACSymbol,
            base: TACSymbol.Var,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmd
    ) : S {
        return this.forget(lhs, toStep, input, whole, l)
    }

    open fun stepExpression(
            lhs: TACSymbol.Var,
            rhs: TACExpr,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ) : S = this.forget(lhs, toStep, input, whole, l.wrapped)

    abstract fun forget(lhs: TACSymbol.Var, toStep: S, input: S, whole: W, l: LTACCmd) : S

    open fun stepReadMemory(
            lhs: TACSymbol.Var,
            loc: TACSymbol,
            base: TACSymbol.Var,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmd
    ) : S = this.forget(lhs, toStep, input, whole, l)
}
