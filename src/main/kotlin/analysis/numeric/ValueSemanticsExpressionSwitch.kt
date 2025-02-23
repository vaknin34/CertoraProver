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

abstract class ValueSemanticsExpressionSwitch<in S, in W, I>(private val valueSemantics: IValueSemantics<S, I, W>, val nondet: I) : IExpressionSwitch<S, W, I> {
    abstract fun interp(
        o: TACSymbol,
        s: S
    ) : I

    override fun mod(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalMod(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun exp(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalExponent(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun bwand(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalBWAnd(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun bwOr(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalBWOr(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun bwxOr(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalBWXOr(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun div(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalDiv(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun shiftLeft(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalShiftLeft(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun shiftRightLogical(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalShiftRightLogical(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun lt(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalLt(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun le(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalLe(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun land(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalLAnd(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun lor(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalLOr(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun eq(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalEq(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun bwNot(
        lhs: TACSymbol.Var,
        s: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalBWNot(v1 = interp(s, input), s = s, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun lnot(
        lhs: TACSymbol.Var,
        s: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalLNot(v1 = interp(s, input), s = s, toStep = toStep, input = input, whole = whole, l = l)
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
    ): I {
        return valueSemantics.evalIte(iSym = i, i = interp(i, input), tSym = t, t = interp(t, input), eSym = e, e = interp(e, input), toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun sdiv(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalSDiv(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun signExtend(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalSignExtend(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun sub(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalSub(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun slt(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalSlt(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun add(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalAdd(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
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
    ): I {
        return valueSemantics.evalAddMod(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, v3 = interp(o3, input), o3 = o3, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun mult(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalMult(v1 = interp(o1, input), o1 = o1, v2 = interp(o2, input), o2 = o2, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun symVar(
        lhs: TACSymbol.Var,
        s: TACSymbol.Var,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalVar(s = s, interp = interp(s, input), toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun const(
        lhs: TACSymbol.Var,
        value: TACSymbol.Const,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return valueSemantics.evalConst(interp = interp(value, input), s = value, toStep = toStep, input = input, whole = whole, l = l)
    }

    override fun havoc(lhs: TACSymbol.Var, toStep: S, input: S, whole: W, wrapped: LTACCmd): I {
        return nondet
    }
}
