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

interface IExpressionSwitch<in S, in W, R> {
    fun stepExpression(
        lhs: TACSymbol.Var,
        rhs: TACExpr,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R {
        return when(rhs) {
            is TACExpr.Sym.Const -> this.const(lhs, rhs.s, toStep, input, whole, l)
            is TACExpr.Sym.Var -> this.symVar(lhs, rhs.s, toStep, input, whole, l)
            is TACExpr.Vec.Mul -> {
                if(rhs.operandsAreSyms()) {
                    this.mult(lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(lhs, toStep, input, whole, l.wrapped)
                }
            }


            is TACExpr.Vec.Add -> {
                if(rhs.operandsAreSyms()) {
                    this.add(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinOp.Sub -> {
                if(rhs.operandsAreSyms()) {
                    this.sub(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinOp.Div -> {
                if(rhs.operandsAreSyms()) {
                    this.div(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinOp.Mod -> {
                if(rhs.operandsAreSyms()) {
                    this.mod(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinOp.Exponent -> {
                if(rhs.operandsAreSyms()) {
                    this.exp(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinOp.BWAnd -> {
                if(rhs.operandsAreSyms()) {
                    this.bwand(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinOp.BWOr -> {
                if(rhs.operandsAreSyms()) {
                    this.bwOr(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinOp.BWXOr -> {
                if(rhs.operandsAreSyms()) {
                    this.bwxOr(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinOp.ShiftLeft -> {
                if(rhs.operandsAreSyms()) {
                    this.shiftLeft(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinOp.ShiftRightLogical -> {
                if(rhs.operandsAreSyms()) {
                    this.shiftRightLogical(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinRel.Gt -> {
                if(rhs.operandsAreSyms()) {
                    this.lt(l.cmd.lhs, rhs.o2AsTACSymbol(),rhs.o1AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinRel.Lt -> {
                if(rhs.operandsAreSyms()) {
                    this.lt(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinRel.Ge -> {
                if(rhs.operandsAreSyms()) {
                    this.le(l.cmd.lhs, rhs.o2AsTACSymbol(),rhs.o1AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinRel.Le -> {
                if(rhs.operandsAreSyms()) {
                    this.le(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinRel.Eq -> {
                if(rhs.operandsAreSyms()) {
                    this.eq(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinBoolOp.LAnd -> {
                if(rhs.operandsAreSyms()) {
                    this.land(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinBoolOp.LOr -> {
                if(rhs.operandsAreSyms()) {
                    this.lor(l.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.UnaryExp.BWNot -> {
                if(rhs.o is TACExpr.Sym) {
                    this.bwNot(l.cmd.lhs, rhs.o.s, toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.UnaryExp.LNot -> {
                if(rhs.o is TACExpr.Sym) {
                    this.lnot(l.cmd.lhs, rhs.o.s, toStep, input, whole, l)
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.TernaryExp.Ite -> {
                if(rhs.i is TACExpr.Sym && rhs.t is TACExpr.Sym && rhs.e is TACExpr.Sym) {
                    this.ite(
                        l.cmd.lhs, rhs.i.s, rhs.t.s, rhs.e.s, toStep, input, whole, l
                    )
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinOp.SDiv -> {
                if(rhs.o1 is TACExpr.Sym && rhs.o2 is TACExpr.Sym) {
                    this.sdiv(
                        l.cmd.lhs, rhs.o1.s, rhs.o2.s, toStep, input, whole, l
                    )
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinOp.SignExtend -> {
                if(rhs.o1 is TACExpr.Sym && rhs.o2 is TACExpr.Sym) {
                    this.signExtend(
                        l.cmd.lhs, rhs.o1.s, rhs.o2.s, toStep, input, whole, l
                    )
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.BinRel.Slt -> {
                if(rhs.o1 is TACExpr.Sym && rhs.o2 is TACExpr.Sym) {
                    this.slt(
                        l.cmd.lhs, rhs.o1.s, rhs.o2.s, toStep, input, whole, l
                    )
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            is TACExpr.TernaryExp.AddMod -> {
                if(rhs.a is TACExpr.Sym && rhs.b is TACExpr.Sym && rhs.n is TACExpr.Sym) {
                    this.addmod(
                       l.cmd.lhs, rhs.a.s, rhs.b.s, rhs.n.s, toStep, input, whole, l
                    )
                } else {
                    this.havoc(l.cmd.lhs, toStep, input, whole, l.wrapped)
                }
            }
            else -> this.havoc(lhs, toStep, input, whole, l.wrapped)
        }
    }

    fun mod(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun exp(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun bwand(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun bwOr(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun bwxOr(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun div(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun shiftLeft(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun shiftRightLogical(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun lt(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun le(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun land(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun lor(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun eq(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun bwNot(
        lhs: TACSymbol.Var,
        s: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun lnot(
        lhs: TACSymbol.Var,
        s: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun ite(lhs: TACSymbol.Var, i: TACSymbol, t: TACSymbol, e: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): R

    fun sdiv(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun signExtend(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun sub(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun slt(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun add(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun addmod(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        o3: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun mult(
        lhs: TACSymbol.Var,
        o1: TACSymbol,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun symVar(
        lhs: TACSymbol.Var,
        s: TACSymbol.Var,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun const(
        lhs: TACSymbol.Var,
        value: TACSymbol.Const,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): R

    fun havoc(lhs: TACSymbol.Var, toStep: S, input: S, whole: W, wrapped: LTACCmd): R
}
