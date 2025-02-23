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

package spec.cvlast

abstract class CVLExpFolder<T> {

    open fun expr(acc: T, exp: CVLExp): T = when (exp) {
        is CVLExp.BinaryExp -> this.binary(acc, exp)
        is CVLExp.UnaryExp -> this.unary(acc, exp)
        is CVLExp.RelopExp -> this.relop(acc, exp)
        is CVLExp.Constant -> this.const(acc, exp)
        is CVLExp.ApplyExp -> this.applyExp(acc, exp)
        is CVLExp.QuantifierExp -> this.quant(acc, exp)
        is CVLExp.SumExp -> this.sum(acc, exp)
        is CVLExp.FieldSelectExp -> this.fieldSel(acc, exp)
        is CVLExp.SetMemExp -> this.setmem(acc, exp)
        is CVLExp.ArrayDerefExp -> this.arrayderef(acc, exp)
        is CVLExp.VariableExp -> this.variable(acc, exp)
        is CVLExp.CondExp -> this.condexp(acc, exp)
        is CVLExp.ArrayLitExp -> this.arrayexp(acc, exp)
        is CVLExp.CastExpr -> this.castExpression(acc, exp)
        is CVLExp.UnresolvedApplyExp -> this.unresolvedApply(acc, exp)
        is CVLExp.AddressFunctionCallExp -> this.addressFunctionCall(acc, exp)
    }

    open fun unresolvedApply(acc: T, exp: CVLExp.UnresolvedApplyExp): T = this.foldSubExpr(acc, *exp.args.toTypedArray())

    open fun addressFunctionCall(acc: T, exp: CVLExp.AddressFunctionCallExp): T = this.foldSubExpr(acc, *exp.args.toTypedArray())

    private fun foldSubExpr(acc: T, vararg e: CVLExp): T = e.fold(acc) { Curr, it ->
        this.expr(Curr, it)
    }

    open fun relop(acc: T, exp: CVLExp.RelopExp): T = when (exp) {
        is CVLExp.RelopExp.ArithRelopExp -> arithRelop(acc, exp)
        is CVLExp.RelopExp.EqExp -> eq(acc, exp)
        is CVLExp.RelopExp.NeExp -> ne(acc, exp)
    }

    open fun arithRelop(acc: T, exp: CVLExp.RelopExp.ArithRelopExp): T = when (exp) {
        is CVLExp.RelopExp.ArithRelopExp.GeExp -> ge(acc, exp)
        is CVLExp.RelopExp.ArithRelopExp.GtExp -> gt(acc, exp)
        is CVLExp.RelopExp.ArithRelopExp.LeExp -> le(acc, exp)
        is CVLExp.RelopExp.ArithRelopExp.LtExp -> lt(acc, exp)
    }

    open fun ge(acc: T, exp: CVLExp.RelopExp.ArithRelopExp.GeExp): T = foldSubExpr(acc, exp.l, exp.r)

    open fun gt(acc: T, exp: CVLExp.RelopExp.ArithRelopExp.GtExp): T = foldSubExpr(acc, exp.l, exp.r)

    open fun le(acc: T, exp: CVLExp.RelopExp.ArithRelopExp.LeExp): T = foldSubExpr(acc, exp.l, exp.r)

    open fun lt(acc: T, exp: CVLExp.RelopExp.ArithRelopExp.LtExp): T = foldSubExpr(acc, exp.l, exp.r)

    open fun eq(acc: T, exp: CVLExp.RelopExp.EqExp): T = foldSubExpr(acc, exp.l, exp.r)

    open fun ne(acc: T, exp: CVLExp.RelopExp.NeExp): T = foldSubExpr(acc, exp.l, exp.r)

    open fun const(acc: T, exp: CVLExp.Constant): T = when (exp) {
        is CVLExp.Constant.BoolLit -> boolLit(acc, exp)
        is CVLExp.Constant.NumberLit -> numberLit(acc, exp)
        is CVLExp.Constant.StringLit -> stringLit(acc, exp)
        is CVLExp.Constant.StructLit -> structLit(acc, exp)
        is CVLExp.Constant.SignatureLiteralExp -> signatureLit(acc, exp)
        is CVLExp.Constant.EnumConstant -> enumConstant(acc, exp)
    }

    open fun enumConstant(acc: T, exp: CVLExp.Constant.EnumConstant): T = acc

    open fun boolLit(acc: T, exp: CVLExp.Constant.BoolLit): T = acc

    open fun numberLit(acc: T, exp: CVLExp.Constant.NumberLit): T = acc

    open fun stringLit(acc: T, exp: CVLExp.Constant.StringLit): T = acc

    open fun structLit(acc: T, exp: CVLExp.Constant.StructLit): T =
        foldSubExpr(acc, *exp.fieldNameToEntry.values.toTypedArray())

    open fun signatureLit(acc: T, exp: CVLExp.Constant.SignatureLiteralExp): T = acc


    open fun applyExp(acc: T, exp: CVLExp.ApplyExp): T =
        when (exp) {
            is CVLExp.ApplyExp.CVLFunction -> call(acc, exp)
            is CVLExp.ApplyExp.ContractFunction -> invokeExp(acc, exp)
            is CVLExp.ApplyExp.Definition -> definition(acc, exp)
            is CVLExp.ApplyExp.Ghost -> ghost(acc, exp)
            is CVLExp.ApplyExp.CVLBuiltIn -> builtin(acc, exp)
        }

    open fun builtin(acc: T, exp: CVLExp.ApplyExp.CVLBuiltIn): T {
        return foldSubExpr(acc, *exp.args.toTypedArray())
    }

    open fun ghost(acc: T, exp: CVLExp.ApplyExp.Ghost): T = foldSubExpr(acc, *exp.args.toTypedArray())

    open fun invokeExp(acc: T, exp: CVLExp.ApplyExp.ContractFunction): T = when(exp) {
        is CVLExp.ApplyExp.ContractFunction.Concrete -> invokeConcreteExp(acc, exp)
        is CVLExp.ApplyExp.ContractFunction.Symbolic -> invokeSymbolicExp(acc, exp)
    }

    open fun invokeConcreteExp(acc: T, exp: CVLExp.ApplyExp.ContractFunction.Concrete): T =
        foldSubExpr(acc, *exp.args.toTypedArray())

    open fun invokeSymbolicExp(acc: T, exp: CVLExp.ApplyExp.ContractFunction.Symbolic): T =
        foldSubExpr(acc, *exp.args.toTypedArray())

    open fun definition(acc: T, exp: CVLExp.ApplyExp.Definition): T =
        foldApply(acc, exp.args)

    open fun castExpression(acc: T, exp: CVLExp.CastExpr): T =
            foldSubExpr(acc, exp.arg)

    open fun call(acc: T, exp: CVLExp.ApplyExp.CVLFunction): T =
        foldApply(acc, exp.args)

    private fun foldApply(
        acc: T, args: List<CVLExp>
    ): T =
        foldSubExpr(acc, *args.toTypedArray())


    open fun binary(acc: T, exp: CVLExp.BinaryExp): T = foldSubExpr(acc, exp.l, exp.r)

    open fun unary(acc: T, exp: CVLExp.UnaryExp): T = foldSubExpr(acc, exp.e)

    open fun quant(acc: T, exp: CVLExp.QuantifierExp): T = expr(acc, exp.body)

    open fun sum(acc: T, exp: CVLExp.SumExp): T = expr(acc, exp.body)

    open fun fieldSel(acc: T, exp: CVLExp.FieldSelectExp): T = expr(acc, exp.structExp)

    open fun setmem(acc: T, exp: CVLExp.SetMemExp): T = foldSubExpr(acc, exp.set, exp.e)

    open fun arrayderef(acc: T, exp: CVLExp.ArrayDerefExp): T = foldSubExpr(acc, exp.array, exp.index)

    abstract fun variable(acc: T, exp: CVLExp.VariableExp): T

    open fun condexp(acc: T, exp: CVLExp.CondExp): T = foldSubExpr(acc, exp.c, exp.e1, exp.e2)

    open fun arrayexp(acc: T, exp: CVLExp.ArrayLitExp): T = foldSubExpr(acc, *exp.elements.toTypedArray())
}
