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
 * A starting point for implementatinos of the [IValueSemantics].
 * All operations are modeled imprecisely by the an element [nondet] of the value domain
 * [I]. This value should represent "don't know".
 *
 * [S] and [W] are the target and hosting state respectively
 */
abstract class AbstractValueSemantics<in S, I, in W> : IValueSemantics<S, I, W> {
    abstract val nondet : I

    override fun evalMod(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalShiftLeft(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalBWXOr(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalExponent(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalBWAnd(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalBWOr(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalShiftRightLogical(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalLt(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalDiv(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalLe(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalEq(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalLAnd(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalSub(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalLOr(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalAdd(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalAddMod(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, v3: I, o3: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalMult(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalLNot(v1: I, s: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalBWNot(v1: I, s: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I = nondet
    override fun evalIte(
        i: I,
        iSym: TACSymbol,
        t: I,
        tSym: TACSymbol,
        e: I,
        eSym: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I = nondet

    override fun evalSlt(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I = nondet

    override fun evalSDiv(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I = nondet

    override fun evalSignExtend(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I = nondet

    override fun evalVar(
        interp: I,
        s: TACSymbol.Var,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I = interp

    override fun evalConst(
        interp: I,
        s: TACSymbol.Const,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I = interp
}
