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

/**
 * Abstract semantics for (a subset of) [vc.data.TACExpr] in some domain [I].
 * These semantics assume the expressions have only symbols as strict subexpressions
 * (as represented by the o1, o2, etc. arguments).
 *
 * [I] is some numeric domain, and [S] is the state which gave the valuation of the operands in [I].
 *
 * As in other cases the toStep argument is a pre-processed version of input (also of type [S]) which may be
 * embedded in some larger state [W]. The l argument provides a context for the evaluation.
 */
interface IValueSemantics<in S, I, in W> {
    fun evalMod(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalShiftLeft(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalBWXOr(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalExponent(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalBWAnd(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalBWOr(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalShiftRightLogical(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalLt(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalDiv(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalLe(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalEq(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalLAnd(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalSub(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalLOr(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalAdd(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalAddMod(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, v3: I, o3: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalMult(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalLNot(v1: I, s: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalBWNot(v1: I, s: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I
    fun evalSlt(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>) : I
    fun evalIte(i: I, iSym: TACSymbol, t: I, tSym: TACSymbol, e: I, eSym: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>) : I
    fun evalSDiv(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>) : I
    fun evalSignExtend(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>) : I
    fun evalVar(
        interp: I,
        s: TACSymbol.Var,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I

    fun evalConst(
        interp: I,
        s: TACSymbol.Const,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ) : I

}
