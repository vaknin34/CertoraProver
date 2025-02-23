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
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * A base for non-relational expression interpreters. In other words, all variables (and constants)
 * can be given independent values in some domain [I]. This valuation for variables is provided
 * by states of type [S] which is a state that is potentially embedded into a larger state [W]
 */
abstract class NonRelationalExpressionInterpreter<S, I, in W> : IExpressionCaseInterpreter<S, W> {
    /**
     * A value in the domain [I] representing a totally unknown, non-deterministic value
     */
    abstract val nondet: I

    /**
     * The [IValueSemantics] for the domain [I].
     */
    abstract val valueSemantics: IValueSemantics<S, I, W>

    override fun forget(lhs: TACSymbol.Var, toStep: S, input: S, whole: W, wrapped: LTACCmd): S {
        return this.assign(toStep, lhs, nondet, input, whole, wrapped)
    }

    /**
     * Assign the value [newValue] to the variable [lhs] in the state [toStep]. [toStep] is a preprocessed
     * version of [input] which was potentially embedded in a larger state [whole]. The assignment occurs in
     * context [wrapped]
     */
    abstract fun assign(toStep: S, lhs: TACSymbol.Var, newValue: I, input: S, whole: W, wrapped: LTACCmd): S


    override fun stepAssignLNot(lhs: TACSymbol.Var, s: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        return valueSemantics.evalLNot(
                this.interp(s, toStep, input, whole, l), s,
                toStep, input, whole, l
        ).let {
            this.assign(toStep, lhs, it, input, whole, l.wrapped)
        }
    }

    override fun stepAssignBWNot(lhs: TACSymbol.Var, s: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = valueSemantics.evalBWNot(
                this.interp(s, toStep, input, whole, l), s,
                toStep, input, whole, l
        )
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)
    }

    override fun stepAssignLe(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = valueSemantics.evalLe(
                this.interp(o1, toStep, input, whole, l),
                o1,
                this.interp(o2, toStep, input, whole, l),
                o2,
                toStep, input, whole, l
        )
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)
    }

    override fun stepAssignMod(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalMod(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignShiftLeft(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalShiftLeft(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignBWXOr(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalBWXOr(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignExponent(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalExponent(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignBWAnd(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalBWAnd(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignBWOr(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalBWOr(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignShiftRightLogical(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalShiftRightLogical(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignLt(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalLt(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignDiv(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalDiv(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignEq(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalEq(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignLAnd(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalLAnd(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)
    }

    override fun stepAssignSub(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalSub(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignLOr(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalLOr(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignAdd(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalAdd(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignAddMod(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, o3: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalAddMod(
            this.interp(o1, toStep, input, whole, l),
            o1,
            this.interp(o2, toStep, input, whole, l),
            o2,
            this.interp(o3, toStep, input, whole, l),
            o3,
            toStep,
            input,
            whole,
            l
        )
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)

    }

    override fun stepAssignMult(lhs: TACSymbol.Var, o1: TACSymbol, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalMult(this.interp(o1, toStep, input, whole, l), o1, this.interp(o2, toStep, input, whole, l), o2, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)
    }

    override fun stepAssignVar(lhs: TACSymbol.Var, s: TACSymbol.Var, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.valueSemantics.evalVar(this.interp(s, toStep, input, whole, l), s, toStep, input, whole, l)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)
    }

    override fun stepAssignSDiv(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S {
        val x = this.valueSemantics.evalSDiv(
            o1 = o1,
            v1 = this.interp(o1, toStep, input, whole, l),
            o2 = o2,
            v2 = this.interp(o2, toStep, input, whole, l),
            toStep = toStep,
            whole = whole,
            input = input,
            l = l
        )
        return this.assign(
            toStep, lhs, x, input, whole, l.wrapped
        )
    }

    override fun stepAssignSignExtend(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S {
        val x = this.valueSemantics.evalSignExtend(
            o1 = o1,
            v1 = this.interp(o1, toStep, input, whole, l),
            o2 = o2,
            v2 = this.interp(o2, toStep, input, whole, l),
            toStep = toStep,
            whole = whole,
            input = input,
            l = l
        )
        return this.assign(
            toStep, lhs, x, input, whole, l.wrapped
        )
    }

    override fun stepAssignIte(
        lhs: TACSymbol.Var,
        iSym: TACSymbol,
        tSym: TACSymbol,
        eSym: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S {
        val x = this.valueSemantics.evalIte(
            i = this.interp(
                iSym, toStep, input, whole, l
            ),
            iSym = iSym,
            t = this.interp(
                tSym, toStep, input, whole, l
            ),
            tSym = tSym,
            e = this.interp(
                eSym, toStep, input, whole, l
            ),
            eSym = eSym,
            toStep = toStep,
            input, whole, l
        )
        return this.assign(
            toStep, lhs, x, input, whole, l.wrapped
        )
    }

    override fun stepAssignSlt(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S {
        val x = this.valueSemantics.evalSlt(
            o1 = o1,
            o2 = o2,
            v1 = this.interp(o1, toStep, input, whole, l),
            v2 = this.interp(o2, toStep, input, whole, l),
            input = input,
            toStep = toStep,
            whole = whole,
            l = l
        )
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)
    }

    /**
     * Provide an interpretation of the symbol [o1]. In general the valuation before pre-processing ([input]) should
     * be preferred as it may have richer information
     */
    abstract fun interp(o1: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I

    override fun stepAssignConst(lhs: TACSymbol.Var, value: BigInteger, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): S {
        val x = this.liftConstant(value)
        return this.assign(toStep, lhs, x, input, whole, l.wrapped)
    }

    /**
     * Lift a constant [value] into the domain [I]
     */
    abstract fun liftConstant(value: BigInteger): I
}
