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

package smtlibutils.algorithms

import smtlibutils.data.*
import smtlibutils.data.SmtIntpFunctionSymbol.Core
import utils.`impossible!`

/**
 * Substitute expressions in a formula according to the mapping [substitution].
 *
 * NB: Currently this class does not account for variables bindings (like quantification), thus it does not implement
 *  standard substitution e.g. for predicate logic.
 * For example `x < 1 \/ forall x. P(x, 5) [x -> 3]` will result in `3 < 1 \/ forall x. P(3, 5)`, which is not what you
 * want in typical logical applications, as standard substitution would yield `3 < 1 \/ forall x. P(x, 5)`.
 *  ==> TODO handle quantified formulas correctly!
 */
class Substitutor(val substitution: Map<SmtExp, SmtExp>, override val smtScript: ISmtScript = SmtScript()) :
    TransformSmt<Unit>() {

    override fun expr(exp: SmtExp, acc: Unit): SmtExp {
        return substitution[exp] ?: super.expr(exp, acc)
    }

    class Scope(val qVars: List<SortedVar>) {
        fun push(newQVars: List<SortedVar>): Scope = Scope(qVars + newQVars)
    }
}

/**
 * not too general, probably implicitly assumes NNF, e.g. ..
 * current use case are expressions in QF_UF
 */
class SortSubstitutor(val substitution: Map<Sort, Sort>, override val smtScript: ISmtScript = SmtScript()) :
    TransformSmt<Unit>() {

    override fun qualId(exp: SmtExp.QualIdentifier, acc: Unit): SmtExp =
        smtScript.qualIdentifier(
            exp.id,
            exp.qualification,
            substituteSort(exp.sort ?: error { "input must be sorted but isn't $this" })
        )

    override fun apply(exp: SmtExp.Apply, acc: Unit): SmtExp {
        val res = super.apply(exp, acc)
        val rankSubstituted =
            Rank(exp.fs.rank.paramSorts.map { substituteSort(it) }, substituteSort(exp.fs.rank.resultSort))
        return if (rankSubstituted == exp.fs.rank) {
            res
        } else {
            when (exp.fs) {
                is Core.Eq -> smtScript.apply(Core.Eq(substituteSort(exp.fs.A)), (res as SmtExp.Apply).args)
                is Core.Distinct -> smtScript.apply(Core.Distinct(substituteSort(exp.fs.A)), (res as SmtExp.Apply).args)
                is Core.Ite -> smtScript.apply(Core.Ite(substituteSort(exp.fs.A)), (res as SmtExp.Apply).args)
                is SmtIntpFunctionSymbol.Array.Select -> smtScript.apply(
                    SmtIntpFunctionSymbol.Array.Select(
                        substituteSort(exp.fs.X),
                        substituteSort(exp.fs.Y)
                    ), (res as SmtExp.Apply).args
                )
                is SmtIntpFunctionSymbol.Array.Store -> smtScript.apply(
                    SmtIntpFunctionSymbol.Array.Store(
                        substituteSort(exp.fs.X),
                        substituteSort(exp.fs.Y)
                    ), (res as SmtExp.Apply).args
                )
                else -> {
                    val fs = SmtUnintpFunctionSymbol(exp.fs.name, rankSubstituted)
                    smtScript.apply(fs, (res as SmtExp.Apply).args)
                }
            }
        }
    }

    fun substituteSort(sort: Sort): Sort = when (sort) {
        is Sort.Symbol -> substitution[sort] ?: sort
        is Sort.Param -> substitution[sort] ?: sort
        is Sort.Apply -> substitution[sort] ?: Sort.Apply(sort.symbol, sort.params.map { substituteSort(it) })
    }
}

object Unletter : TransformSmt<Unit>() {
    override val smtScript: ISmtScript = SmtScript()

    override fun letExp(exp: SmtExp.Let, acc: Unit): SmtExp {
        val defsTransformed =
            exp.defs.map { varBinding -> smtScript.varBinding(varBinding.id, expr(varBinding.def, acc)) }
        val bodyTransformed = expr(exp.body, acc)
        return smtScript.letExpr(defsTransformed, bodyTransformed).unlet()
    }

    fun unlet(exp: SmtExp): SmtExp = Unletter.expr(exp, Unit)

}

/**
 * Note that by default this class rebuilds every subexpression using [smtScript] -- choosing [smtScript] allows to
 * choose behaviours e.g. [SmtScript] will track declarations, [FactorySmtScript] will just build, one day we may
 * have a caching [ISmtScript] that only builds unique terms once.  --> this means that, besides the transformation,
 * there can be side effects to the [smtScript] object.
 * */
abstract class TransformSmt<ACC> {
    abstract val smtScript: ISmtScript
    open val cmdAccFactory: ((Cmd) -> ACC)? = null

    open fun smt(smt: SMT) = smtScript.smt(smt.cmds.map { cmd(it) })

    open fun smt(smt: SMT, acc: ACC) = smtScript.smt(smt.cmds.map { cmd(it, acc) })

    open fun cmd(cmd: Cmd): Cmd = cmd(
        cmd,
        (cmdAccFactory ?: error { "either provide a cmdAccFactory, or call cmd with an ACC!" })(cmd)
    )

    open fun cmd(cmd: Cmd, acc: ACC): Cmd = when (cmd) {
        is Cmd.NoOp -> cmd
        is Cmd.Custom -> throw UnsupportedOperationException("cannot use smt transformations with custom command \"$cmd\"")
        is Cmd.Goal -> goalCmd(cmd, acc)
        is Cmd.Model -> modelCmd(cmd, acc)
        is Cmd.ValDefList -> throw UnsupportedOperationException("cannot transform a val def list (might consider implementing)")
        is Cmd.Assert -> assertCmd(cmd, acc)
        is Cmd.DeclareSort -> declareSort(cmd, acc)
        is Cmd.DeclareDatatypes -> declareDatatypes(cmd, acc)
        is Cmd.DeclareConst -> declareConst(cmd, acc)
        is Cmd.DeclareFun -> declareFun(cmd, acc)
        is Cmd.DefineFun -> defineFun(cmd, acc)
        is Cmd.CheckSat -> checkSat(cmd, acc)
        is Cmd.GetUnsatCore -> getUnsatCore(cmd, acc)
        is Cmd.Reset -> reset(cmd, acc)
        is Cmd.ResetAssertions -> resetAssertions(cmd, acc)
        is Cmd.GetModel -> getModel(cmd, acc)
        is Cmd.GetValue -> getValue(cmd, acc)
        is Cmd.SetOption -> setOption(cmd, acc)
        is Cmd.GetInfo -> getInfo(cmd, acc)
        is Cmd.SetLogic -> setLogic(cmd, acc)
        is Cmd.StatsCmd -> statsCmd(cmd, acc)
        is Cmd.Push -> push(cmd, acc)
        is Cmd.Pop -> pop(cmd, acc)
    }

    open fun goalCmd(cmd: Cmd.Goal, acc: ACC): Cmd = smtScript.goalCmd(cmd.exprs.map { expr(it, acc) })
    open fun modelCmd(cmd: Cmd.Model, acc: ACC): Cmd = smtScript.modelCmd(cmd.defs.map { cmd(it, acc) })
    open fun assertCmd(cmd: Cmd.Assert, acc: ACC): Cmd = smtScript.assertCmd(expr(cmd.e, acc))

    open fun declareSort(cmd: Cmd.DeclareSort, acc: ACC): Cmd =
        smtScript.declareSort(cmd.sortDec)

    open fun declareDatatypes(cmd: Cmd.DeclareDatatypes, acc: ACC): Cmd =
        smtScript.declareDatatypes(cmd.sortDecs, cmd.constructorDecListList)

    open fun declareConst(cmd: Cmd.DeclareConst, acc: ACC): Cmd =
        smtScript.declareConst(cmd.name, cmd.sort)

    open fun declareFun(cmd: Cmd.DeclareFun, acc: ACC): Cmd =
        smtScript.declareFun(cmd.name, cmd.param_sorts, cmd.result_sort)

    open fun defineFun(cmd: Cmd.DefineFun, acc: ACC): Cmd =
        smtScript.defineFun(cmd.name, cmd.params, cmd.res_sort, expr(cmd.definition, acc))

    open fun checkSat(cmd: Cmd.CheckSat, acc: ACC): Cmd = smtScript.checkSat()
    open fun reset(cmd: Cmd.Reset, acc: ACC): Cmd = smtScript.reset()
    open fun resetAssertions(cmd: Cmd.ResetAssertions, acc: ACC): Cmd = smtScript.resetAssertions()
    open fun getModel(cmd: Cmd.GetModel, acc: ACC): Cmd = smtScript.getModel()

    open fun getValue(cmd: Cmd.GetValue, acc: ACC): Cmd = smtScript.getValue(cmd.expList)

    open fun getUnsatCore(cmd: Cmd.GetUnsatCore, acc: ACC): Cmd = smtScript.getUnsatCore()
    open fun getInfo(cmd: Cmd.GetInfo, acc: ACC): Cmd = smtScript.getInfo(cmd.name)

    open fun push(cmd: Cmd.Push, acc: ACC): Cmd = smtScript.push(cmd.n)
    open fun pop(cmd: Cmd.Pop, acc: ACC): Cmd = smtScript.pop(cmd.n)

    open fun setOption(cmd: Cmd.SetOption, acc: ACC): Cmd = smtScript.setOption(cmd.name, cmd.value)
    open fun setLogic(cmd: Cmd.SetLogic, acc: ACC): Cmd = smtScript.setLogic(cmd.logic)
    open fun statsCmd(cmd: Cmd.StatsCmd, acc: ACC): Cmd = smtScript.stats(cmd.stats)

    open fun expr(exp: SmtExp, acc: ACC): SmtExp = when (exp) {
        is SmtExp.QualIdentifier -> qualId(exp, acc)
        is SmtExp.Apply -> apply(exp, acc)
        is SmtExp.Lambda -> lambda(exp, acc)
        is SmtExp.Let -> letExp(exp, acc)
        is SmtExp.Quant -> quant(exp, acc)
        is SmtExp.BitvectorLiteral -> bitVecLit(exp, acc)
        is SmtExp.BoolLiteral -> boolLit(exp, acc)
        is SmtExp.IntLiteral -> intLit(exp, acc)
        is SmtExp.DecLiteral -> decLit(exp, acc)
        is SmtExp.AnnotatedExp -> annotatedExp(exp, acc)
        is SmtExp.PlaceHolder -> `impossible!`
    }

    open fun qualId(exp: SmtExp.QualIdentifier, acc: ACC): SmtExp =
        this.qualId(exp.id, exp.qualification, exp.sort, acc)

    open fun qualId(id: Identifier, qualification: Sort?, sort: Sort?, acc: ACC): SmtExp =
        smtScript.qualIdentifier(id, qualification, sort)

    open fun apply(exp: SmtExp.Apply, acc: ACC): SmtExp =
        this.apply(exp.fs, exp.args, exp.sort, acc)

    // TODO: implement these field-by-field methods for the expressions that don't have it...
    open fun apply(fs: SmtFunctionSymbol, args: List<SmtExp>, sort: Sort?, acc: ACC): SmtExp =
        smtScript.apply(fs, args.map { expr(it, acc) }, sort)

    open fun lambda(exp: SmtExp.Lambda, acc: ACC): SmtExp = smtScript.lambda(exp.args, expr(exp.e, acc), exp.sort)

    open fun letExp(exp: SmtExp.Let, acc: ACC): SmtExp =
        smtScript.letExpr(
            exp.defs.map { smtScript.varBinding(it.id, expr(it.def, acc)) },
            expr(exp.body, acc),
            exp.sort
        )

    open fun quant(exp: SmtExp.Quant, acc: ACC): SmtExp = when (exp) {
        is SmtExp.Quant.Exists -> existsExp(exp, acc)
        is SmtExp.Quant.ForAll -> forallExp(exp, acc)
    }

    open fun forallExp(exp: SmtExp.Quant.ForAll, acc: ACC): SmtExp =
        smtScript.forAll(exp.boundVars, expr(exp.body, acc))

    open fun existsExp(exp: SmtExp.Quant.Exists, acc: ACC): SmtExp =
        smtScript.exists(exp.boundVars, expr(exp.body, acc))

    open fun bitVecLit(exp: SmtExp.BitvectorLiteral, acc: ACC): SmtExp = smtScript.bitvector(exp.n, exp.width)
    open fun boolLit(exp: SmtExp.BoolLiteral, acc: ACC): SmtExp = smtScript.boolLit(exp.b)
    open fun intLit(exp: SmtExp.IntLiteral, acc: ACC): SmtExp = smtScript.number(exp.i)
    open fun decLit(exp: SmtExp.DecLiteral, acc: ACC): SmtExp = smtScript.decimal(exp.d)

    open fun annotatedExp(exp: SmtExp.AnnotatedExp, acc: ACC): SmtExp =
        smtScript.annotatedExp(expr(exp.innerExp, acc), exp.annotation)
}


abstract class TransformSmtWithResult<ACC,
        CR : TransformSmtWithResult.TransformSmtResultCmd,
        ER : TransformSmtWithResult.TransformSmtResultExp> {

    open val smtScript: ISmtScript = SmtScript() //TODO should be NoopScript

    abstract val expERFactory: ((SmtExp) -> ER)
    abstract val cmdCRFactory: ((Cmd) -> CR)

    open fun cmd(cmd: Cmd, acc: ACC): CR = when (cmd) {
        is Cmd.NoOp -> noopCmd(cmd, acc)
        is Cmd.Custom -> throw UnsupportedOperationException("cannot use smt transformations with custom command \"$cmd\"")
        is Cmd.Goal -> goalCmd(cmd, acc)
        is Cmd.Model -> modelCmd(cmd, acc)
        is Cmd.Assert -> assertCmd(cmd, acc)
        is Cmd.ValDefList -> throw UnsupportedOperationException("cannot use smt transformations with val def list \"$cmd\"")
        is Cmd.DeclareSort -> declareSort(cmd, acc)
        is Cmd.DeclareDatatypes -> declareDatatypes(cmd, acc)
        is Cmd.DeclareConst -> declareConst(cmd, acc)
        is Cmd.DeclareFun -> declareFun(cmd, acc)
        is Cmd.DefineFun -> defineFun(cmd, acc)
        is Cmd.CheckSat -> checkSat(cmd, acc)
        is Cmd.Reset -> reset(cmd, acc)
        is Cmd.GetModel -> getModel(cmd, acc)
        is Cmd.GetValue -> getValue(cmd, acc)
        is Cmd.GetUnsatCore -> getUnsatCore(cmd, acc)
        is Cmd.GetInfo -> getInfo(cmd, acc)
        is Cmd.SetOption -> setOption(cmd, acc)
        is Cmd.SetLogic -> setLogic(cmd, acc)
        is Cmd.StatsCmd -> statsCmd(cmd, acc)
        is Cmd.ResetAssertions -> cmdCRFactory(cmd)
        is Cmd.Push -> cmdCRFactory(cmd)
        is Cmd.Pop -> cmdCRFactory(cmd)
    }

    open fun noopCmd(cmd: Cmd.NoOp, acc: ACC): CR = cmdCRFactory(cmd)
    open fun goalCmd(cmd: Cmd.Goal, acc: ACC): CR = cmdCRFactory(cmd)
    open fun modelCmd(cmd: Cmd.Model, acc: ACC): CR = cmdCRFactory(cmd)
    open fun assertCmd(cmd: Cmd.Assert, acc: ACC): CR =
        cmdCRFactory(smtScript.assertCmd(expr(cmd.e, acc).exp))

    open fun declareSort(cmd: Cmd.DeclareSort, acc: ACC): CR =
        cmdCRFactory(smtScript.declareSort(cmd.sortDec))

    open fun declareDatatypes(cmd: Cmd.DeclareDatatypes, acc: ACC): CR =
        cmdCRFactory(smtScript.declareDatatypes(cmd.sortDecs, cmd.constructorDecListList))

    open fun declareConst(cmd: Cmd.DeclareConst, acc: ACC): CR =
        cmdCRFactory(smtScript.declareConst(cmd.name, cmd.sort))

    open fun declareFun(cmd: Cmd.DeclareFun, acc: ACC): CR =
        cmdCRFactory(smtScript.declareFun(cmd.name, cmd.param_sorts, cmd.result_sort))

    open fun defineFun(cmd: Cmd.DefineFun, acc: ACC): CR =
        cmdCRFactory(
            smtScript.defineFun(
                cmd.name,
                cmd.params,
                cmd.res_sort,
                expr(cmd.definition, acc).exp
            )
        )

    open fun checkSat(cmd: Cmd.CheckSat, acc: ACC): CR = cmdCRFactory(smtScript.checkSat())
    open fun reset(cmd: Cmd.Reset, acc: ACC): CR = cmdCRFactory(smtScript.reset())
    open fun getModel(cmd: Cmd.GetModel, acc: ACC): CR = cmdCRFactory(smtScript.getModel())

    open fun getValue(cmd: Cmd.GetValue, acc: ACC): CR = cmdCRFactory(smtScript.getModel())
    open fun getUnsatCore(cmd: Cmd.GetUnsatCore, acc: ACC): CR = cmdCRFactory(smtScript.getUnsatCore())
    open fun getInfo(cmd: Cmd.GetInfo, acc: ACC): CR = cmdCRFactory(smtScript.getInfo(cmd.name))

    open fun setOption(cmd: Cmd.SetOption, acc: ACC): CR =
        cmdCRFactory(smtScript.setOption(cmd.name, cmd.value))

    open fun setLogic(cmd: Cmd.SetLogic, acc: ACC): CR = cmdCRFactory(smtScript.setLogic(cmd.logic))
    open fun statsCmd(cmd: Cmd.StatsCmd, acc: ACC): CR = cmdCRFactory(smtScript.stats(cmd.stats))

    open fun expr(exp: SmtExp, acc: ACC): ER = when (exp) {
        is SmtExp.QualIdentifier -> qualId(exp, acc)
        is SmtExp.Apply -> apply(exp, acc)
        is SmtExp.Lambda -> lambda(exp, acc)
        is SmtExp.Let -> letExp(exp, acc)
        is SmtExp.Quant.ForAll -> forallExp(exp, acc)
        is SmtExp.Quant.Exists -> existsExp(exp, acc)
        is SmtExp.BitvectorLiteral -> bitVecLit(exp, acc)
        is SmtExp.BoolLiteral -> boolLit(exp, acc)
        is SmtExp.IntLiteral -> intLit(exp, acc)
        is SmtExp.DecLiteral -> decLit(exp, acc)
        is SmtExp.AnnotatedExp -> annotatedExp(exp, acc)
        is SmtExp.PlaceHolder -> `impossible!`
    }

    open fun qualId(exp: SmtExp.QualIdentifier, acc: ACC): ER =
        expERFactory(smtScript.qualIdentifier(exp.id, exp.qualification, exp.sort))

    open fun apply(exp: SmtExp.Apply, acc: ACC): ER =
        expERFactory(smtScript.apply(exp.fs, exp.args.map { expr(it, acc).exp }, exp.sort))

    open fun lambda(exp: SmtExp.Lambda, acc: ACC): ER =
        expERFactory(smtScript.lambda(exp.args, expr(exp.e, acc).exp, exp.sort))

    open fun letExp(exp: SmtExp.Let, acc: ACC): ER =
        expERFactory(
            smtScript.letExpr(
                exp.defs.map { smtScript.varBinding(it.id, expr(it.def, acc).exp) },
                expr(exp.body, acc).exp,
                exp.sort
            )
        )

    open fun forallExp(exp: SmtExp.Quant.ForAll, acc: ACC): ER =
        expERFactory(smtScript.forAll(exp.boundVars, expr(exp.body, acc).exp))

    open fun existsExp(exp: SmtExp.Quant.Exists, acc: ACC): ER =
        expERFactory(smtScript.exists(exp.boundVars, expr(exp.body, acc).exp))

    open fun bitVecLit(exp: SmtExp.BitvectorLiteral, acc: ACC): ER =
        expERFactory(smtScript.bitvector(exp.n, exp.width))

    open fun boolLit(exp: SmtExp.BoolLiteral, acc: ACC): ER =
        expERFactory(smtScript.boolLit(exp.b))

    open fun intLit(exp: SmtExp.IntLiteral, acc: ACC): ER = expERFactory(smtScript.number(exp.i))

    open fun decLit(exp: SmtExp.DecLiteral, acc: ACC): ER = expERFactory(smtScript.decimal(exp.d))

    open fun annotatedExp(exp: SmtExp.AnnotatedExp, acc: ACC): ER =
        expERFactory(smtScript.annotatedExp(expr(exp, acc).exp, exp.annotation))

    interface TransformSmtResultExp {
        val exp: SmtExp
    }

    interface TransformSmtResultCmd {
        val cmd: Cmd
    }
}

open class AndOrFlattener<ACC>(override val smtScript: ISmtScript = SmtScript()) : TransformSmt<ACC>() {
    override fun apply(fs: SmtFunctionSymbol, args: List<SmtExp>, sort: Sort?, acc: ACC): SmtExp {
        return when (fs) {
            is Core.LAnd -> {
                val argsTransformed = args.map { expr(it, acc) }
                val conjuncts = argsTransformed.flatMap { arg ->
                    if (arg.isApp(Core.LAnd::class)) {
                        (arg as SmtExp.Apply).args
                    } else {
                        listOf(arg)
                    }
                }
                super.apply(fs, conjuncts, sort, acc)
            }
            is Core.LOr -> {
                val argsTransformed = args.map { expr(it, acc) }
                val disjuncts = argsTransformed.flatMap { arg ->
                    if (arg.isApp(Core.LOr::class)) {
                        (arg as SmtExp.Apply).args
                    } else {
                        listOf(arg)
                    }
                }
                super.apply(fs, disjuncts, sort, acc)
            }
            else -> super.apply(fs, args, sort, acc)
        }
    }
}
