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

import datastructures.stdcollections.*
import smtlibutils.algorithms.TransformSmt
import smtlibutils.algorithms.TraverseSmt


class SortAndNormalize(val script: ISmtScript, val symbolTable: SmtSymbolTable, val logic: Logic) {
    constructor(script: SmtScript, logic: Logic) : this(script, script.symbolTable, logic)

    val normalizer = BasicNormalizations(script, symbolTable, logic)
    val sorter = Sorter(script, symbolTable)

    fun expr(exp: SmtExp): SmtExp =
        normalizer.expr(exp, Unit).let {
            sorter.expr(it, Sorter.TypeScope.getEmpty(symbolTable))
        }

    fun smt(smt: SMT): SMT = normalizer.smt(smt, Unit).let {
        sorter.smt(it, Sorter.TypeScope.getEmpty(symbolTable))
    }
}

/**
 *
 * @param defaultConstantType allows to provide a sort that should be assumed for symbols that haven't been declared
 *  in [symbolTable].
 */
class Sorter(
    override val smtScript: ISmtScript, val symbolTable: SmtSymbolTable,
    private val defaultConstantType: Sort? = null
) : TransformSmt<Sorter.TypeScope>() {
    constructor(smtScript: SmtScript, defaultConstantType: Sort? = null) : this(
        smtScript,
        smtScript.symbolTable,
        defaultConstantType
    )


    override val cmdAccFactory: ((Cmd) -> TypeScope) = { _ -> TypeScope.getEmpty(symbolTable, defaultConstantType) }

    fun sort(exp: HasSmtExp) =
        exp.mapExp { sort(it) }

    fun sort(exp: SmtExpWithComment) =
        SmtExpWithComment(expr(exp.exp, TypeScope.getEmpty(symbolTable, defaultConstantType)), exp.comment)

    fun sort(exp: SmtExp) = expr(exp, TypeScope.getEmpty(symbolTable, defaultConstantType))

    fun sort(exp: SmtExp, typeScope: TypeScope) = expr(exp, typeScope)

    open class TypeScope(
        val env: List<SortedVar>,
        val symbolTable: SmtSymbolTable,
        private val defaultConstantType: Sort? = null
    ) {

        fun scope(sortedVars: List<SortedVar>) = TypeScope(env + sortedVars, symbolTable, defaultConstantType)

        fun lookUp(name: String): Rank {
            // look into env
            val itr = env.listIterator(env.size)
            while (itr.hasPrevious()) {
                val curr = itr.previous()
                if (curr.id == name) {
                    return Rank(curr.sort)
                }
            }
            // look into symbol table
            return symbolTable.lookUpFunction(name)?.functionSymbol?.rank
                ?: defaultConstantType?.let { Rank(it) }
                ?: throw SmtSortException("$this: symbol $name not found in symbol table")
        }

        companion object {
            fun getEmpty(symbolTable: SmtSymbolTable, defaultConstantType: Sort? = null): TypeScope =
                TypeScope(listOf(), symbolTable, defaultConstantType)
        }
    }

    /** automatically updates [smtScript.symbolTable] */
    override fun declareConst(cmd: Cmd.DeclareConst, acc: TypeScope): Cmd.DeclareConst {
        return smtScript.declareConst(cmd.name, cmd.sort)
    }

    /** automatically updates [smtScript.symbolTable] */
    override fun declareFun(cmd: Cmd.DeclareFun, acc: TypeScope): Cmd.DeclareFun {
        return smtScript.declareFun(cmd.name, cmd.param_sorts, cmd.result_sort)
    }

    override fun defineFun(cmd: Cmd.DefineFun, acc: TypeScope): Cmd.DefineFun {
        val definition =
            expr(cmd.definition, TypeScope.getEmpty(symbolTable, defaultConstantType).scope(cmd.params))
        check(definition.sort == cmd.res_sort)
        return smtScript.defineFun(cmd.name, cmd.params, cmd.res_sort, definition)
    }

    override fun assertCmd(cmd: Cmd.Assert, acc: TypeScope): Cmd.Assert {
        val exp = expr(cmd.e, acc)
        check(exp.sort == Sort.BoolSort)
        return smtScript.assertCmd(exp)
    }

    override fun apply(exp: SmtExp.Apply, acc: TypeScope): SmtExp.Apply {
        val params = exp.args.map { expr(it, acc) }
        val fs = smtScript.instantiateParamSorts(
            exp.fs,
            params.map { it.sort ?: error { "$it should have a sort at this point." } })
        check(fs.rank.resultSort !is Sort.Param)
        return smtScript.apply(fs, params, fs.rank.resultSort)
    }

    override fun forallExp(exp: SmtExp.Quant.ForAll, acc: TypeScope): SmtExp {
        val body = expr(exp.body, acc.scope(exp.boundVars))
        check(body.sort == Sort.BoolSort)
        return smtScript.forAll(exp.boundVars, body)
    }

    override fun existsExp(exp: SmtExp.Quant.Exists, acc: TypeScope): SmtExp {
        val e = expr(exp.body, acc.scope(exp.boundVars))
        check(e.sort == Sort.BoolSort)
        return smtScript.exists(exp.boundVars, e)
    }

    override fun lambda(exp: SmtExp.Lambda, acc: TypeScope): SmtExp {
        val e = expr(exp.e, acc.scope(exp.args))
        return smtScript.lambda(exp.args, e, Sort.arraySort(exp.args.map { it.sort }, e.sort ?: error { "$e must have a sort at this point." }))
    }

    override fun letExp(exp: SmtExp.Let, acc: TypeScope): SmtExp.Let {
        val varBindings = exp.defs.map { varBinding -> smtScript.varBinding(varBinding.id, expr(varBinding.def, acc)) }
        val body = expr(
            exp.body,
            acc.scope(varBindings.map {
                smtScript.sortedVar(
                    it.id,
                    it.def.sort ?: error { "$it should have a sort at this point." })
            })
        )
        return smtScript.letExpr(varBindings, body, body.sort ?: error { "$body must have a sort at this point." })
    }

    override fun qualId(exp: SmtExp.QualIdentifier, acc: TypeScope): SmtExp {
        check(exp.qualification == null)

        if (exp.id is Identifier.Indexed) {
            SmtExp.BitvectorLiteral.fromIndexedIdentifier(exp.id, smtScript, Logic.ALL)?.let {
                return it
            }
        }
        /** Note that it's rather an internal convention here to convert the [Rank] to an `Array`-sort, not something
         * that is covered by the SMTLib standard. */
        return smtScript.qualIdentifier(exp.id, null, acc.lookUp(exp.id.sym).asArraySort)
    }
}

/**
 *  - resolves expressions like `(_ bv3 256)` to bit vector literals.
 *  - replaces z3 specific function symbols like [SmtIntpFunctionSymbol.BV.BinOp.Z3Specific.BvUDivI] with their SMTLib
 *    counterparts, if such are available
 *
 *  current known use case: parsing back models or CNFs from z3
 */
class BasicNormalizations(
    override val smtScript: ISmtScript,
    val symbolTable: SmtSymbolTable,
    val logic: Logic,
) :
    TransformSmt<Unit>() {
    override fun qualId(exp: SmtExp.QualIdentifier, acc: Unit): SmtExp {
        if (exp.id is Identifier.Indexed) {
            val bvLit = SmtExp.BitvectorLiteral.fromIndexedIdentifier(exp.id, smtScript, logic)
            if (bvLit != null) return bvLit
        }
        return super.qualId(exp, acc)
    }

    override fun apply(exp: SmtExp.Apply, acc: Unit): SmtExp {
        if (exp.fs is SmtIntpFunctionSymbol.BV.BinOp.Z3Specific &&
            exp.fs.smtLibEquivalent != null
        ) {
            return smtScript.apply(exp.fs.smtLibEquivalent, exp.args.map { expr(it, Unit) })
        }
        return super.apply(exp, Unit)
    }

}


class FindLogic : TraverseSmt() {
    var logic: Logic? = null

    override fun setLogic(cmd: Cmd.SetLogic) {
        check(logic == null) { "this only works when there is exactly one set-logic command in the input" }
        logic = Logic.fromString(cmd.logic)
        super.setLogic(cmd)
    }

    companion object {
        fun findLogic(cmds: Collection<Cmd>): Logic {
            val fl = FindLogic()
            cmds.forEach { fl.cmd(it) }
            return fl.logic ?: Logic.ALL
        }

        fun findLogic(smt: SMT): Logic = findLogic(smt.cmds)

    }
}
