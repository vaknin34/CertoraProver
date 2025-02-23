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

package smtlibutils.data

import java.math.BigDecimal
import java.math.BigInteger

interface ISmtScript {

    open operator fun invoke(expr: ISmtScript.() -> SmtExp): SmtExp = expr()

    fun declareSort(name: String, arity: Int): Cmd.DeclareSort = declareSort(SortDec(name, arity))

    fun declareSort(sortDec: SortDec): Cmd.DeclareSort

    fun declareDatatypes(
        sortDecs: List<SortDec>,
        constructorDecListList: List<List<DatatypeConstructorDec>>
    ): Cmd.DeclareDatatypes

    fun defineFun(name: String, param_sorts: List<SortedVar>, res_sort: Sort, definition: SmtExp): Cmd.DefineFun

    fun stats(sl: List<Stat>): Cmd.StatsCmd

    fun getInfo(name: String): Cmd.GetInfo

    fun setOption(name: String, v: String): Cmd.SetOption

    fun setLogic(value: String): Cmd.SetLogic

    fun declareFun(name: String, param_sorts: List<Sort>, result_sort: Sort): Cmd.DeclareFun

    fun declareConst(name: String, sort: Sort): Cmd.DeclareConst

    fun assertCmd(exp: SmtExp): Cmd.Assert

    fun checkSat(): Cmd.CheckSat

    fun reset(): Cmd.Reset

    fun resetAssertions(): Cmd.ResetAssertions

    fun push(n: Int): Cmd.Push

    fun pop(n: Int): Cmd.Pop

    fun getModel(): Cmd.GetModel

    fun getValue(expList: List<SmtExp>): Cmd.GetValue

    fun getUnsatCore(): Cmd.GetUnsatCore

    fun commentCmd(s: String): Cmd.NoOp

    fun goalCmd(exprs: List<SmtExp>): Cmd.Goal

    fun modelCmd(defs: List<Cmd>): Cmd.Model

    fun boolLit(bool: Boolean): SmtExp.BoolLiteral

    fun number(int: BigInteger): SmtExp.IntLiteral

    fun number(num: String): SmtExp.IntLiteral

    fun decimal(dec: BigDecimal): SmtExp.DecLiteral

    fun decimal(dec: String): SmtExp.DecLiteral

    fun hex(hexValue: String): SmtExp.BitvectorLiteral

    fun binary(binaryValue: String): SmtExp.BitvectorLiteral

    fun bitvector(n: BigInteger, width: Int): SmtExp.BitvectorLiteral

    fun lambda(vars: List<SortedVar>, body: SmtExp): SmtExp.Lambda

    fun lambda(vars: List<SortedVar>, body: SmtExp, sort: Sort?): SmtExp.Lambda

    fun letExpr(defs: List<VarBinding>, body: SmtExp): SmtExp.Let

    fun letExpr(defs: List<VarBinding>, body: SmtExp, sort: Sort?): SmtExp.Let

    fun apply(qid: SmtExp.QualIdentifier, el: List<SmtExp>): SmtExp.Apply

    fun apply(qid: SmtExp.QualIdentifier, el: List<SmtExp>, sort: Sort?): SmtExp.Apply

    fun apply(fs: SmtFunctionSymbol, el: List<SmtExp>): SmtExp.Apply

    fun apply(fs: SmtFunctionSymbol, el: List<SmtExp>, sort: Sort?): SmtExp.Apply

    fun apply(fs: SmtFunctionSymbol, vararg ops: SmtExp): SmtExp.Apply

    fun forAll(bv: List<SortedVar>, exp: SmtExp): SmtExp.Quant.ForAll

    fun annotatedExp(innerExp: SmtExp, annot: SmtAnnotation): SmtExp.AnnotatedExp

    fun exists(bv: List<SortedVar>, exp: SmtExp): SmtExp.Quant.Exists

    fun stat(name: String, value: String): Stat

    fun simpleIdentifier(id: String): Identifier.Simple

    fun indexedIdentifier(id: String, il: List<String>): Identifier.Indexed

    fun varBinding(sym: String, e: SmtExp): VarBinding

    fun qualIdentifier(id: Identifier): SmtExp.QualIdentifier

    fun qualIdentifier(id: Identifier, qualSort: Sort?): SmtExp.QualIdentifier

    fun qualIdentifier(id: Identifier, qualSort: Sort?, sort: Sort?): SmtExp.QualIdentifier

    fun sortedVar(name: String, sort: Sort): SortedVar

    fun simpleSort(id: Identifier): Sort

    fun constructSort(id: Identifier, sl: List<Sort>): Sort

    fun smt(lines: List<Cmd>): SMT

    fun comment(s: String) = commentCmd(s)

    fun namedAnnotation(name: String): SmtAnnotation.NamedAnnotation

    // convenience functions

    val True: SmtExp

    val False: SmtExp

    fun not(op: SmtExp): SmtExp

    fun and(vararg ops: SmtExp): SmtExp

    fun and(ops: List<SmtExp>): SmtExp

    infix fun SmtExp.and(other: SmtExp): SmtExp = and(this, other)

    fun or(vararg ops: SmtExp): SmtExp

    fun or(ops: List<SmtExp>): SmtExp

    infix fun SmtExp.or(other: SmtExp): SmtExp = or(this, other)

    infix fun SmtExp.implies(other: SmtExp): SmtExp

    /** Creates a [QualIdentifier] with a simple id. */
    fun id(simpleId: String, sort: Sort? = null) = qualIdentifier(
        id = simpleIdentifier(simpleId),
        qualSort = null,
        sort = sort
    )

    fun forAllOrId(bv: List<SortedVar>, exp: SmtExp): SmtExp =
        if (bv.isEmpty()) exp
        else forAll(bv, exp)

    fun existsOrId(bv: List<SortedVar>, exp: SmtExp): SmtExp =
        if (bv.isEmpty()) exp
        else exists(bv, exp)

    fun negateLiteral(lit: SmtExp): SmtExp {
        assert(lit.isBooleanLiteral())
        val polarity = !lit.isAtom()
        return if (polarity) (lit as SmtExp.Apply).args[0] else not(lit)
    }

    fun distinct(ops: List<SmtExp>): SmtExp =
        if (ops.size < 2) True
        else {
            val sort = ops.first().sort
            check(sort != null)
            assert(ops.all { it.sort == sort })
            apply(SmtIntpFunctionSymbol.Core.Distinct(sort), ops)
        }

    infix fun SmtExp.eq(other: SmtExp): SmtExp = eq(this, other)

    fun eq(vararg ops: SmtExp): SmtExp = eq(ops.toList())

    fun eq(ops: List<SmtExp>): SmtExp =
        if (ops.size < 2) True
        else {
            val sort = ops.first().sort
            check(sort != null) { "got a null sort when it's not expected (operands to eq: $ops)" }
            check(ops.all { it.sort == sort }) { "not different sorts in operands to eq" }
            apply(SmtIntpFunctionSymbol.Core.Eq(sort), ops)
        }

    infix fun SmtExp.le(other: SmtExp): SmtExp =
        compare(this, other, SmtIntpFunctionSymbol.IRA::Le)

    infix fun SmtExp.lt(other: SmtExp): SmtExp =
        compare(this, other, SmtIntpFunctionSymbol.IRA::Lt)

    infix fun SmtExp.ge(other: SmtExp): SmtExp =
        compare(this, other, SmtIntpFunctionSymbol.IRA::Ge)

    infix fun SmtExp.gt(other: SmtExp): SmtExp =
        compare(this, other, SmtIntpFunctionSymbol.IRA::Gt)

    infix fun SmtExp.bvadd256(other: SmtExp): SmtExp =
        apply(SmtIntpFunctionSymbol.BV.BinOp.BvAdd(256), this, other)

    /**
     * Infix syntax for apply(SmtIntpFunctionSymbol.BV.Rel.BvULt(256), [this], [other]).
     */
    infix fun SmtExp.bvult256(other: SmtExp): SmtExp =
        apply(SmtIntpFunctionSymbol.BV.Rel.BvULt(256), this, other)

    /**
     * Applies bitvector256 addition (sum) on the given collection of bitvector SmtExps.
     */
    fun bvadd256(terms: Collection<SmtExp>): SmtExp = terms.reduce { a, b -> a bvadd256 b }

    private fun compare(op1: SmtExp, op2: SmtExp, comparator: (Sort) -> SmtIntpFunctionSymbol.IRA): SmtExp =
        apply(comparator(op1.sort ?: SmtIntpFunctionSymbol.defaultSortParamN), op1, op2)

    /**
     * Return an [ISmtScript] whose symbol table is the given one; other state that this script contained (if any)
     * can be preserved (decided by implementation of this method).
     *
     * Background: [ISmtScript]s can have different kinds of state, among that a [SmtSymbolTable] carrying declaration
     * information. Sometimes this declaration info is outdated, e.g. though a `(reset)` command.  */
    fun withSymbolTable(symbolTable: SmtSymbolTable): SmtScript

    /** Returns "raw" function symbol, i.e. maybe not all sorts are instantiated. */
    fun getFunctionSymbol(qid: SmtExp.QualIdentifier): SmtFunctionSymbol {
        var fs = SmtFunctionSymbol.fromIdentifier(qid.id)
        if (qid.qualification != null) {
            fs = fs.instantiateResultSort(qid.qualification)
        }
        return fs
    }

    fun instantiateResultSort(fs: SmtFunctionSymbol, resultSort: Sort): SmtFunctionSymbol =
        fs.instantiateResultSort(resultSort)

    fun instantiateParamSorts(fs: SmtFunctionSymbol, paramSorts: List<Sort>): SmtFunctionSymbol =
        fs.instantiateParamSorts(paramSorts)

    /** Returns an independent copy of this. */
    fun fork(): ISmtScript

}
