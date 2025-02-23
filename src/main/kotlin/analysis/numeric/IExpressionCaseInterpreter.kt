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
import java.math.BigInteger

/**
 * An [IExpressionInterpreter] that special cases all expression forms
 * when all strict sub-expressions are sumbols. The default implementation of
 * [IExpressionInterpreter.stepExpression] cases over an expression and calls
 * the relevant stepAssign* function.
 */
interface IExpressionCaseInterpreter<S, in W> : IExpressionInterpreter<S, W> {

    val dispatcher get() = object : IExpressionSwitch<S, W, S> {
        override fun mod(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignMod(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun exp(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignExponent(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun bwand(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignBWAnd(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun bwOr(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignBWOr(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun bwxOr(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignBWXOr(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun div(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignDiv(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun shiftLeft(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignShiftLeft(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun shiftRightLogical(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignShiftRightLogical(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun lt(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignLt(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun le(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignLe(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun land(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignLAnd(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun lor(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignLOr(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun eq(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignEq(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun bwNot(
            lhs: TACSymbol.Var,
            s: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignBWNot(lhs, s, toStep, input, whole, l)
        }

        override fun lnot(
            lhs: TACSymbol.Var,
            s: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignLNot(lhs, s, toStep, input, whole, l)
        }

        override fun ite(
            lhs: TACSymbol.Var,
            i: TACSymbol,
            t: TACSymbol,
            e: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignIte(
                lhs = lhs,
                iSym = i,
                tSym = t,
                eSym = e,
                toStep = toStep,
                input = input,
                whole = whole,
                l = l
            )
        }

        override fun sdiv(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignSDiv(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun signExtend(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignSignExtend(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun sub(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignSub(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun slt(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignSlt(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun add(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignAdd(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun mult(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignMult(lhs, o1, o2, toStep, input, whole, l)
        }

        override fun symVar(
            lhs: TACSymbol.Var,
            s: TACSymbol.Var,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignVar(lhs, s, toStep, input, whole, l)
        }

        override fun const(
            lhs: TACSymbol.Var,
            value: TACSymbol.Const,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignConst(lhs, value.value, toStep, input, whole, l)
        }

        override fun havoc(lhs: TACSymbol.Var, toStep: S, input: S, whole: W, wrapped: LTACCmd): S {
            return forget(lhs, toStep, input, whole, wrapped)
        }

        override fun addmod(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            o3: TACSymbol,
            toStep: S,
            input: S,
            whole: W,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): S {
            return stepAssignAddMod(lhs, o1, o2, o3, toStep, input, whole, l)
        }

    }

    /**
     * Model the effects of [rhs] being assigned into [lhs] in state [toStep].
     * [toStep] is derived from [input] which itself was embedded in state [whole].
     *
     * This step takes place in context [l]
     *
     * By default, for each form of [rhs] if the sub-expressions are symbols it
     * will call stepAssign*;, e.g. [stepAssignAdd] for [TACExpr.Vec.Add] and so on.
     *
     * If this does not hold, it will use the special [forget] function to model the expression
     * as "havoc.
     */
    override fun stepExpression(
        lhs: TACSymbol.Var,
        rhs: TACExpr,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S {
        return dispatcher.stepExpression(lhs, rhs, toStep, input, whole, l)
    }

    fun stepAssignSDiv(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignSignExtend(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignIte(
        lhs: TACSymbol.Var,
        iSym: TACSymbol,
        tSym: TACSymbol,
        eSym: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignLNot(
        lhs: TACSymbol.Var,
        s: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignBWNot(
        lhs: TACSymbol.Var,
        s: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignMod(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignShiftLeft(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignBWXOr(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignExponent(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignBWAnd(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignBWOr(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignShiftRightLogical(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignLt(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignDiv(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignLe(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignEq(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignLAnd(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignSub(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun forget(
        lhs: TACSymbol.Var,
        toStep: S,
        input: S,
        whole: W,
        wrapped: LTACCmd
    ): S

    fun stepAssignLOr(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignAdd(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S


    fun stepAssignAddMod(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        o3: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S


    fun stepAssignMult(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignVar(
        lhs: TACSymbol.Var,
        s: TACSymbol.Var,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignConst(
        lhs: TACSymbol.Var,
        value: BigInteger,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S

    fun stepAssignSlt(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ) : S
}
