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
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * A starting point for a case interpreter, where all functions simply [forget] the value being
 * assigned.
 */
abstract class AbstractExpressionCaseInterpreter<S, in W> : IExpressionCaseInterpreter<S, W> {
    override fun stepAssignLNot(
            lhs: TACSymbol.Var,
            s: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignBWNot(
            lhs: TACSymbol.Var,
            s: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignMod(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignShiftLeft(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignBWXOr(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignExponent(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignBWAnd(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignBWOr(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignShiftRightLogical(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignLt(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignDiv(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignLe(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignEq(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignLAnd(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignSub(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignLOr(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignAdd(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignAddMod(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        o3: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignMult(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignVar(
            lhs: TACSymbol.Var,
            s: TACSymbol.Var,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignConst(
            lhs: TACSymbol.Var,
            value: BigInteger,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignSlt(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignSDiv(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignSignExtend(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)

    override fun stepAssignIte(
        lhs: TACSymbol.Var,
        iSym: TACSymbol,
        tSym: TACSymbol,
        eSym: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S = this.forget(lhs, toStep, input, whole, l.wrapped)
}
