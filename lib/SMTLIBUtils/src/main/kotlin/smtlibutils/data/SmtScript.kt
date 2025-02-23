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

import log.*
import smtlibutils.data.Cmd.*
import java.math.BigDecimal
import java.math.BigInteger
import java.util.*

private val logger = Logger(SMTLIBUtilsLoggerTypes.SMTLIBUTILS)

abstract class AbstractFactorySmtScript : ISmtScript {

    override fun defineFun(name: String, param_sorts: List<SortedVar>, res_sort: Sort, definition: SmtExp): DefineFun =
        DefineFun(name, param_sorts, res_sort, definition)

    override fun stats(sl: List<Stat>): StatsCmd = StatsCmd(sl)

    override fun getInfo(name: String): GetInfo = GetInfo(name)

    override fun setOption(name: String, v: String): SetOption = SetOption(name, v)

    override fun setLogic(value: String): SetLogic = SetLogic(value)

    override fun declareFun(name: String, param_sorts: List<Sort>, result_sort: Sort): DeclareFun =
        DeclareFun(name, param_sorts, result_sort)

    override fun declareConst(name: String, sort: Sort): DeclareConst =
        DeclareConst(name, sort)

    override fun assertCmd(exp: SmtExp): Assert = Assert(exp)

    override fun checkSat(): CheckSat = CheckSat()

    override fun reset(): Reset = Reset()

    override fun resetAssertions(): ResetAssertions = ResetAssertions()

    override fun push(n: Int): Push = Push(n)

    override fun pop(n: Int): Pop = Pop(n)

    override fun getModel(): GetModel = GetModel()

    override fun getValue(expList: List<SmtExp>): GetValue = GetValue(expList)

    override fun getUnsatCore(): GetUnsatCore = GetUnsatCore()

    override fun stat(name: String, value: String): Stat = Stat(name, value)

    override fun commentCmd(s: String): NoOp = NoOp(s)

    override fun goalCmd(exprs: List<SmtExp>): Goal = Goal(exprs)

    override fun modelCmd(defs: List<Cmd>): Model = Model(defs)

    override fun number(int: BigInteger): SmtExp.IntLiteral = SmtExp.IntLiteral(int)

    override fun number(num: String): SmtExp.IntLiteral = SmtExp.IntLiteral(BigInteger(num))

    override fun decimal(dec: BigDecimal): SmtExp.DecLiteral = SmtExp.DecLiteral(dec)

    override fun decimal(dec: String): SmtExp.DecLiteral = SmtExp.DecLiteral(BigDecimal(dec))

    override fun hex(hexValue: String): SmtExp.BitvectorLiteral {
        check(hexValue.startsWith("#x"))
        val withOutPrefix = hexValue.substring(2)
        return SmtExp.BitvectorLiteral(BigInteger(withOutPrefix, 16), withOutPrefix.length * 4)
    }

    override fun binary(binaryValue: String): SmtExp.BitvectorLiteral {
        check(binaryValue.startsWith("#b"))
        val withOutPrefix = binaryValue.substring(2)
        return SmtExp.BitvectorLiteral(BigInteger(withOutPrefix, 2), withOutPrefix.length)
    }

    override fun bitvector(n: BigInteger, width: Int): SmtExp.BitvectorLiteral = SmtExp.BitvectorLiteral(n, width)

    override fun lambda(vars: List<SortedVar>, body: SmtExp): SmtExp.Lambda = lambda(vars, body, sort = null)

    override fun lambda(vars: List<SortedVar>, body: SmtExp, sort: Sort?): SmtExp.Lambda =
        SmtExp.Lambda(vars, body, sort)

    override fun letExpr(defs: List<VarBinding>, body: SmtExp): SmtExp.Let = letExpr(defs, body, null)

    override fun letExpr(defs: List<VarBinding>, body: SmtExp, sort: Sort?): SmtExp.Let {
        return SmtExp.Let(defs, body, sort)
    }


    override fun apply(qid: SmtExp.QualIdentifier, el: List<SmtExp>): SmtExp.Apply =
        apply(qid, el, null)

    override fun apply(qid: SmtExp.QualIdentifier, el: List<SmtExp>, sort: Sort?): SmtExp.Apply {
        return apply(getFunctionSymbol(qid), el, sort)
    }

    /** Note that this tries to restore the sort from the function symbol. Allows for preserving the sort when doing
     * certain transformations. */
    override fun apply(fs: SmtFunctionSymbol, el: List<SmtExp>) = SmtExp.Apply(fs, el, fs.getConcreteResultSortOrNull())

    override fun apply(fs: SmtFunctionSymbol, el: List<SmtExp>, sort: Sort?) = SmtExp.Apply(fs, el, sort)

    override fun forAll(bv: List<SortedVar>, exp: SmtExp): SmtExp.Quant.ForAll {
        check(bv.isNotEmpty())
        return SmtExp.Quant.ForAll(bv, exp)
    }

    override fun annotatedExp(innerExp: SmtExp, annot: SmtAnnotation): SmtExp.AnnotatedExp =
        SmtExp.AnnotatedExp(innerExp, annot)

    override fun exists(bv: List<SortedVar>, exp: SmtExp): SmtExp.Quant.Exists {
        check(bv.isNotEmpty())
        return SmtExp.Quant.Exists(bv, exp)
    }

    override fun boolLit(bool: Boolean): SmtExp.BoolLiteral {
        return SmtExp.BoolLiteral(bool)
    }

    override fun simpleIdentifier(id: String): Identifier.Simple {
        return Identifier.Simple(id)
    }

    override fun indexedIdentifier(id: String, il: List<String>): Identifier.Indexed {
        return Identifier.Indexed(id, il)
    }

    override fun varBinding(sym: String, e: SmtExp): VarBinding = VarBinding(sym, e)

    override fun qualIdentifier(id: Identifier): SmtExp.QualIdentifier = qualIdentifier(id, null, null)

    override fun qualIdentifier(id: Identifier, qualSort: Sort?): SmtExp.QualIdentifier =
        qualIdentifier(id, qualSort, null)

    override fun qualIdentifier(id: Identifier, qualSort: Sort?, sort: Sort?): SmtExp.QualIdentifier =
        SmtExp.QualIdentifier(id, qualSort, sort)

    override fun sortedVar(name: String, sort: Sort): SortedVar = SortedVar(name, sort)

    override fun declareSort(sortDec: SortDec): DeclareSort = DeclareSort(sortDec)

    override fun declareDatatypes(
        sortDecs: List<SortDec>,
        constructorDecListList: List<List<DatatypeConstructorDec>>
    ): DeclareDatatypes = DeclareDatatypes(sortDecs, constructorDecListList)

    override fun simpleSort(id: Identifier): Sort = Sort.Symbol(SortSymbol.fromIdentifier(id))

    override fun constructSort(id: Identifier, sl: List<Sort>): Sort = Sort.Apply(SortSymbol.fromIdentifier(id), sl)

    override fun smt(lines: List<Cmd>): SMT = SMT(lines)

    override fun namedAnnotation(name: String): SmtAnnotation.NamedAnnotation = SmtAnnotation.NamedAnnotation(name)

    // implementations of convenience functions

    override fun apply(fs: SmtFunctionSymbol, vararg ops: SmtExp): SmtExp.Apply = this.apply(fs, ops.toList())

    override val True: SmtExp = SmtExp.BoolLiteral.True// this.apply(SmtIntpFunctionSymbol.Core.True)

    override val False: SmtExp = SmtExp.BoolLiteral.False // this.apply(SmtIntpFunctionSymbol.Core.False)

    override fun not(op: SmtExp): SmtExp = this.apply(SmtIntpFunctionSymbol.Core.LNot, op)

    override fun and(vararg ops: SmtExp): SmtExp = and(ops.toList())

    override fun and(ops: List<SmtExp>): SmtExp =
        when (ops.size) {
            0 -> this.True
            1 -> ops.first()
            else -> this.apply(SmtIntpFunctionSymbol.Core.LAnd, ops)
        }

    override fun or(vararg ops: SmtExp): SmtExp = or(ops.toList())

    override fun or(ops: List<SmtExp>): SmtExp =
        when (ops.size) {
            0 -> this.False
            1 -> ops.first()
            else -> this.apply(SmtIntpFunctionSymbol.Core.LOr, ops)
        }

    override infix fun SmtExp.implies(other: SmtExp): SmtExp = apply(SmtIntpFunctionSymbol.Core.LImplies, this, other)

    override fun withSymbolTable(symbolTable: SmtSymbolTable): SmtScript {
        return SmtScript(symbolTable.copy()) // make a fresh copy, to avoid aliasing problems
    }


}

object FactorySmtScript : AbstractFactorySmtScript() {
    override fun fork() = this
}

class SmtSortException(val msg: String) : Exception(msg)

/**
 * An [ISmtScript] that both constructs SMT Ast elements and tracks declarations in a symbol table.
 *
 * Should maybe be called `SmtScriptWithSymbolTable` or so...
 *
 * NB: be careful when using this in a parallel setting -- there are potential race conditions, e.g. between `register*`
 *  and `fork()`
 * */
open class SmtScript(val symbolTable: SmtSymbolTable) : AbstractFactorySmtScript() {
    constructor() : this(SmtSymbolTable())

    override fun setLogic(value: String): SetLogic {
        return super.setLogic(value)
    }

    override fun declareSort(name: String, arity: Int): DeclareSort {
        symbolTable.registerDeclSort(simpleIdentifier(name), arity)
        return super.declareSort(name, arity)
    }

    override fun declareDatatypes(
        sortDecs: List<SortDec>,
        constructorDecListList: List<List<DatatypeConstructorDec>>
    ): DeclareDatatypes {
        val declareDatatypes = super.declareDatatypes(sortDecs, constructorDecListList)
        symbolTable.registerDeclDatatypes(declareDatatypes, this)
        return declareDatatypes
    }

    override fun defineFun(
        name: String,
        param_sorts: List<SortedVar>,
        res_sort: Sort,
        definition: SmtExp
    ): DefineFun {
        symbolTable.registerDeclFun(simpleIdentifier(name), param_sorts.map { it.sort }, res_sort)
        return super.defineFun(name, param_sorts, res_sort, definition)
    }

    override fun declareFun(name: String, param_sorts: List<Sort>, result_sort: Sort): DeclareFun {
        symbolTable.registerDeclFun(simpleIdentifier(name), param_sorts, result_sort)
        return super.declareFun(name, param_sorts, result_sort)
    }

    override fun declareConst(name: String, sort: Sort): DeclareConst {
        symbolTable.registerDeclFun(simpleIdentifier(name), listOf(), sort)
        return super.declareConst(name, sort)
    }

    override fun simpleSort(id: Identifier): Sort {
        val symb = SortSymbol.Intp.fromIdentifier(id)
            ?: SortSymbol.UserDefined(id, 0) // TODO: do a proper lookup
        return Sort.Symbol(symb)
    }

    override fun apply(qid: SmtExp.QualIdentifier, el: List<SmtExp>, sort: Sort?): SmtExp.Apply {
        return super.apply(getFunctionSymbol(qid), el, sort)
    }

    override fun getFunctionSymbol(qid: SmtExp.QualIdentifier): SmtFunctionSymbol {
        var fs = SmtFunctionSymbol.fromIdentifier(qid.id, symbolTable)
        if (qid.qualification != null) {
            fs = instantiateResultSort(fs, qid.qualification)
        }
        return fs
    }

    override fun constructSort(id: Identifier, sl: List<Sort>): Sort =
        Sort.Apply(SortSymbol.fromIdentifier(id, symbolTable), sl)

    override fun fork(): ISmtScript = SmtScript(symbolTable.copy())
}

object EmptySymbolTable : SmtSymbolTable() {
    override fun registerDeclFun(
        name: Identifier,
        param_sorts: List<Sort>,
        res_sort: Sort,
        isDatatypeConstructor: Boolean
    ) {
        throw UnsupportedOperationException("not allowed in EmptySymbolTable")
    }

    override fun registerDeclSort(name: Identifier, arity: Int) {
        throw UnsupportedOperationException("not allowed in EmptySymbolTable")
    }

}

open class SmtSymbolTable private constructor(private val scopeStack: Stack<Scope>) {
    constructor() : this(createEmptyScopeStack())

    companion object {
        private fun createEmptyScopeStack(): Stack<Scope> {
            val s = Stack<Scope>()
            s.push(Scope(mutableMapOf(), mutableMapOf()))
            return s
        }
    }

    open fun registerDeclSort(name: Identifier, arity: Int) {
        scopeStack.peek().declaredSorts[name] = Declaration.Srt(name, arity)
    }

    open fun registerDeclFun(
        name: Identifier, param_sorts: List<Sort>, res_sort: Sort,
        isDatatypeConstructor: Boolean = false
    ) {
        if (scopeStack.peek().declaredFuns[name].let {
                it != null && (it.param_sorts != param_sorts || it.res_sort != res_sort)
            }) {
            throw SmtSortException("function $name already declared/defined")
        }
        scopeStack.peek().declaredFuns[name] = Declaration.Fun(name, param_sorts, res_sort, isDatatypeConstructor)
    }

    fun hasSortDecl(name: String): Boolean = lookUpSort(name) != null

    fun hasFunDecl(name: String): Boolean = lookUpFunction(name) != null

    fun lookUpSort(name: String): Declaration.Srt? {
        check(scopeStack.size == 1) { "need to implement proper stack lookup when this check fails" }
        return scopeStack.peek().declaredSorts[FactorySmtScript.simpleIdentifier(name)]
    }

    /**
     * Look up the given [Identifier] in our internal symbol table (which was created from the explicit declarations in
     * the SMT file.
     */
    fun lookUpFunction(id: Identifier): Declaration.Fun? {
        if (id !is Identifier.Simple) {
            logger.warn { "attempted to look up function symbol with indexed identifier in SMT symbol table: $id" }
            return null
        }
        return scopeStack.peek().declaredFuns[id]
    }

    /**
     * Same as [lookUpFunction] but accepts a String that will be made into an [Identifier.Simple] for the lookup.
     */
    fun lookUpFunction(name: String): Declaration.Fun? {
        check(scopeStack.size == 1) { "need to implement proper stack lookup when this check fails" }
        return scopeStack.peek().declaredFuns[FactorySmtScript.simpleIdentifier(name)]
    }

    /**
     * Returns all functions/constants that are declared in the current scope (via declare-fun or declare-const
     * commands).
     * TODO: status of defined-funs is a bit unclear for these purposes, we might introduce an internal flag to separate
     * those; right now a define-fun induces a declare-fun, in this class..
     */
    fun getAllDeclaredFuns(): List<Declaration.Fun> {
        check(scopeStack.size == 1) { "need to implement proper stack lookup when this check fails" }
        return scopeStack.peek().declaredFuns.values.toList()
    }

    fun getAllDeclaredSorts(): List<Declaration.Srt> {
        check(scopeStack.size == 1) { "need to implement proper stack lookup when this check fails" }
        return scopeStack.peek().declaredSorts.values.toList()
    }

    fun copy(): SmtSymbolTable {
        check(scopeStack.size == 1) { "need to implement proper stack lookup when this check fails" }
        val stackCopy = run {
            val cp = Stack<Scope>()
            cp.push(scopeStack.peek().copy())
            cp
        }
        return SmtSymbolTable(stackCopy)
    }

    override fun toString(): String {
        return this.scopeStack.joinToString(", ", "[", "]")
    }

    /**
     * [script] is used to generate identifiers
     */
    fun registerDeclDatatypes(declareDatatypes: DeclareDatatypes, script: ISmtScript) {
        declareDatatypes.sortDecs.zip(declareDatatypes.constructorDecListList).map { (sortDec, constructorDecList) ->
            val sortId = script.simpleIdentifier(sortDec.name)
            registerDeclSort(sortId, sortDec.arity)
            val dtSort = Sort.Symbol(SortSymbol.UserDefined(sortId, sortDec.arity))
            constructorDecList.forEach { constructorDec ->
                /* constructor */
                registerDeclFun(
                    script.simpleIdentifier(constructorDec.name),
                    constructorDec.selectors.map { it.sort },
                    dtSort,
                    isDatatypeConstructor = true,
                )
                /* selectors */
                constructorDec.selectors.forEach { selector ->
                    registerDeclFun(script.simpleIdentifier(selector.id), listOf(dtSort), selector.sort)
                }
            }
        }
    }

    fun isDatatypeConstructor(fs: SmtFunctionSymbol): Boolean = lookUpFunction(fs.name)?.isDatatypeConstructor ?: false

    fun isDatatypeConstructor(id: Identifier): Boolean = lookUpFunction(id)?.isDatatypeConstructor ?: false

    class Scope(
        val declaredFuns: MutableMap<Identifier, Declaration.Fun>,
        val declaredSorts: MutableMap<Identifier, Declaration.Srt>,
    ) {
        fun copy(): Scope {
            return Scope(declaredFuns.toMutableMap(), declaredSorts.toMutableMap())
        }

        override fun toString(): String {
            val sb = StringBuilder()
            if (declaredSorts.isNotEmpty()) {
                sb.append(declaredSorts)
            }
            if (declaredFuns.isNotEmpty()) {
                sb.append(declaredFuns)
            }
            return "$sb, "
        }
    }

    sealed class Declaration {

        data class Fun(
            val id: Identifier,
            val param_sorts: List<Sort>,
            val res_sort: Sort,
            val isDatatypeConstructor: Boolean,
        ) : Declaration() {
            val functionSymbol: SmtFunctionSymbol =
                SmtUnintpFunctionSymbol(id, Rank(param_sorts, res_sort))

            fun toCommand(script: ISmtScript) = script.declareFun(id.sym, param_sorts, res_sort)
        }

        data class Srt(val name: Identifier, val arity: Int) {
            val sortSymbol: SortSymbol = SortSymbol.UserDefined(name, arity)
            val sort = Sort.Symbol(sortSymbol)
            fun toCommand(script: ISmtScript) = script.declareSort(name.sym, arity)
        }
    }
}


class SharingSmtScript : SmtScript() {

    private val applyTerms: MutableMap<Triple<SmtFunctionSymbol, List<SmtExp>, Sort?>, SmtExp.Apply> = mutableMapOf()

    private val qualIds: MutableMap<Pair<Identifier, Sort?>, SmtExp.QualIdentifier> = mutableMapOf()

    private val simpleIdentifiers: MutableMap<String, Identifier.Simple> = mutableMapOf()

    private val indexedIdentifiers: MutableMap<Pair<String, List<String>>, Identifier.Indexed> = mutableMapOf()

    /** We assume all sorts/ranks have been fully instantiated (using [Sorter]) before this script is called.
     *  Actually, a typical use case will be to use and initialize (fill cache) this inside sorter.
     */
    private val functionSymbols: MutableMap<Pair<Identifier, Rank>, SmtFunctionSymbol> = mutableMapOf()

    override fun instantiateParamSorts(fs: SmtFunctionSymbol, paramSorts: List<Sort>): SmtFunctionSymbol {
        val fsInstantiated = super.instantiateParamSorts(fs, paramSorts)
        return functionSymbols.getOrPut(
            fsInstantiated.name to fsInstantiated.rank,
            { fsInstantiated }) // TODO unify the identifiers here???
    }

    override fun instantiateResultSort(fs: SmtFunctionSymbol, resultSort: Sort): SmtFunctionSymbol {
        val fsInstantiated = super.instantiateResultSort(fs, resultSort)
        return functionSymbols.getOrPut(
            fsInstantiated.name to fsInstantiated.rank,
            { fsInstantiated }) // TODO unify the identifiers here???
    }

    // TODO lambda, let, quantifiers, ...?, override equals methods in all the AST classes (only object identity)

    override fun apply(fs: SmtFunctionSymbol, el: List<SmtExp>): SmtExp.Apply =
        fs.getConcreteResultSortOrNull().let { sort ->
            applyTerms.getOrPut(Triple(fs, el, sort), { super.apply(fs, el, sort) })
        }

    override fun apply(fs: SmtFunctionSymbol, el: List<SmtExp>, sort: Sort?): SmtExp.Apply =
        applyTerms.getOrPut(Triple(fs, el, sort), { super.apply(fs, el, sort) })

    override fun qualIdentifier(id: Identifier, qualSort: Sort?, sort: Sort?): SmtExp.QualIdentifier {
        check(qualSort == null)
        { "$this: qualification should have been resolved when using this script" }
        return qualIds.getOrPut(id to sort, { super.qualIdentifier(id, qualSort, sort) })
    }

    override fun simpleIdentifier(id: String): Identifier.Simple =
        simpleIdentifiers.getOrPut(id, { super.simpleIdentifier(id) })

    override fun indexedIdentifier(id: String, il: List<String>): Identifier.Indexed =
        indexedIdentifiers.getOrPut(id to il, { super.indexedIdentifier(id, il) })

    override fun withSymbolTable(symbolTable: SmtSymbolTable): SmtScript {
        throw UnsupportedOperationException("should be implemented once we put this class into use")
    }

    override fun fork(): ISmtScript {
        throw UnsupportedOperationException("should be implemented once we put this class into use")
    }
}

