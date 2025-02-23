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
import utils.`impossible!`
import java.util.*


/**
 * Holds a [result] which is supposedly updated during traversal, and lots of [process] functions for submitting input
 * to the collector. As a convenience, all these functions return [result], but note that it will be the same object
 * no matter when in the lifetime of the collector it is called.
 *
 * Standard use case is to create a collector, sumbit something for processing and collecting the result. But it's also
 * possible to create a collector, submit several things for processing and using the result only in the end.
 */
abstract class SmtCollector<T> : TraverseSmt() {
    abstract val result : T

    /** Just a bit of fun to make a function return [result] */
    private inline fun rr(f : () -> Unit) : T {
        f()
        return result
    }

    /** useful for calling from a function that gets vararg */
    fun process(exps: Array<out HasSmtExp>) = rr {
        exps.forEach { expr(it.exp) }
    }

    @JvmName("process1")
    fun process(vararg exps: HasSmtExp) = rr {
        exps.forEach { expr(it.exp) }
    }

    fun process(expss: Array<out Collection<HasSmtExp>>) = rr {
        expss.forEach { exps ->
            exps.forEach { expr(it.exp) }
        }
    }

    @JvmName("process2")
    fun process(vararg expss: Collection<HasSmtExp>) = rr {
        process(expss)
    }

    fun process(smt: SMT) = rr {
        smt(smt)
    }

    @JvmName("process3")
    fun process(lines : Collection<Cmd>) = rr {
        lines.forEach { cmd(it) }
    }
}

abstract class SmtSetCollector<T> : SmtCollector<Set<T>>() {
    override val result = mutableSetOf<T>()

    fun add(t: T) = result.add(t)
}

abstract class SmtPropertyChecker(val initial : Boolean) : SmtCollector<Boolean>() {
    private var flag = initial
    override val result get() = flag
    fun setFlag() {
        flag = !initial
        stop()
    }
}


class CollectSubexpressions : SmtSetCollector<SmtExp>() {
    override fun expr(exp: SmtExp) {
        result.add(exp)
        super.expr(exp)
    }
}

/**
 * Collects all identifiers [SmtExp.QualIdentifier] in an [SMT]-object/command/expression.
 * Somewhat analogous to "getFreeVariables" methods in other places; used for a variety of purposes.
 */
class CollectQualIds : SmtSetCollector<SmtExp.QualIdentifier>() {
    companion object {
        fun collectQualIds(vararg expss: Collection<HasSmtExp>) = CollectQualIds().process(expss)
        fun collectQualIds(vararg exps: HasSmtExp) = CollectQualIds().process(exps)
    }

    val boundVars = Stack<SortedVar>()

    override fun forallExp(exp: SmtExp.Quant.ForAll) {
        exp.boundVars.forEach { boundVars.push(it) }
        super.forallExp(exp)
        exp.boundVars.forEach { _ -> boundVars.pop() }
    }

    override fun existsExp(exp: SmtExp.Quant.Exists) {
        exp.boundVars.forEach { boundVars.push(it) }
        super.existsExp(exp)
        exp.boundVars.forEach { _ -> boundVars.pop() }
    }

    override fun qualId(exp: SmtExp.QualIdentifier) {
        if (exp.id is Identifier.Simple) {
            if (!boundVars.any { it.id == exp.id.sym }) {
                add(exp)
            }
        } else {
            add(exp)
        }
    }
}

class CollectSorts : SmtSetCollector<Sort>() {
    companion object {
        fun collectSorts(lines : Collection<Cmd>) = CollectSorts().process(lines)
    }

    override fun qualId(exp: SmtExp.QualIdentifier) {
        add(exp.sort ?: error { "expression is not sorted" })
    }

    override fun apply(exp: SmtExp.Apply) {
        exp.fs.rank.paramSorts.forEach { add(it) }
        add(exp.fs.rank.resultSort)
        super.apply(exp)
    }
}

class CollectFunctionSymbols : SmtSetCollector<SmtFunctionSymbol>() {
    companion object {
        fun collectFuncSymbols(exp : HasSmtExp) = CollectFunctionSymbols().process(exp)
    }
    override fun apply(exp: SmtExp.Apply) {
        add(exp.fs)
        super.apply(exp)
    }
}

class CollectDefinitionsSmt(private val definedVars: Set<SmtExp.QualIdentifier>) :
    SmtCollector<Map<SmtExp.QualIdentifier, SmtExp>>() {
    override val result = mutableMapOf<SmtExp.QualIdentifier, SmtExp>()

    override fun apply(exp: SmtExp.Apply) {
        // is exp a definition??
        if (exp.fs is SmtIntpFunctionSymbol.Core.Eq && exp.args.size == 2) {
            if (exp.args[0] in definedVars) result[exp.args[0] as SmtExp.QualIdentifier] = exp.args[1]
            if (exp.args[1] in definedVars) result[exp.args[1] as SmtExp.QualIdentifier] = exp.args[0]
        }
        // is exp a conjunction?
        if (exp.fs is SmtIntpFunctionSymbol.Core.LAnd) {
            super.apply(exp) // go recursively into conjunction
        }
        // nothing more to do (in particular, ignore everything that is below a function symbol that's neither "=" or "and"
    }
}

class ContainsIte : SmtPropertyChecker(false) {
    companion object {
        fun containsIte(exp: HasSmtExp) = ContainsIte().process(exp)
    }
    override fun apply(exp: SmtExp.Apply) {
        if (exp.fs is SmtIntpFunctionSymbol.Core.Ite) {
            setFlag()
        }
        super.apply(exp)
    }
}

class IsSorted : SmtPropertyChecker(true) {
    companion object {
        fun isSorted(exp: HasSmtExp) = IsSorted().process(exp)
        fun isSorted(exps: Collection<HasSmtExp>) = IsSorted().process(exps)
        fun isSorted(smt: SMT) = IsSorted().process(smt)
    }

    override fun expr(exp: SmtExp) {
        if (exp.sort == null) {
            setFlag()
        }
        super.expr(exp)
    }

    override fun apply(exp: SmtExp.Apply) {
        if (exp.fs.rank.paramSorts.any { it.isParametrized() } || exp.fs.rank.resultSort.isParametrized()) {
            setFlag()
        }
        super.apply(exp)
    }
}

class IsGround : SmtPropertyChecker(true) {
    companion object {
        fun isGround(exp: HasSmtExp) = IsGround().process(exp)
    }

    override fun existsExp(exp: SmtExp.Quant.Exists) {
        setFlag()
        super.existsExp(exp)
    }

    override fun forallExp(exp: SmtExp.Quant.ForAll) {
        setFlag()
        super.forallExp(exp)
    }
}

/**
 * A base implementations for traversing smt expressions recursively.
 */
abstract class TraverseSmt(
    private val inlineDefineFuns: Boolean = false,
    initialDefineFuns: List<Cmd.DefineFun> = listOf()
) {
    private val defineFuns = initialDefineFuns.toMutableList()
    protected open val script: ISmtScript = FactorySmtScript

    private var quit = false

    fun stop() {
        quit = true
    }

    open fun smt(smt: SMT) {
        if (!quit) {
            smt.cmds.forEach { cmd(it) }
        }
    }

    open fun cmd(cmd: Cmd) {
        if (!quit) {
            when (cmd) {
                is Cmd.NoOp -> noopCmd(cmd)
                is Cmd.Custom -> throw UnsupportedOperationException("cannot use smt transformations with custom command \"$cmd\"")
                is Cmd.Goal -> goalCmd(cmd)
                is Cmd.Model -> modelCmd(cmd)
                is Cmd.ValDefList -> throw UnsupportedOperationException("cannot use smt transformations with val def list \"$cmd\"")
                is Cmd.Assert -> assertCmd(cmd)
                is Cmd.DeclareSort -> declareSort(cmd)
                is Cmd.DeclareDatatypes -> declareDatatypes(cmd)
                is Cmd.DeclareConst -> declareConst(cmd)
                is Cmd.DeclareFun -> declareFun(cmd)
                is Cmd.DefineFun -> defineFun(cmd)
                is Cmd.CheckSat -> checkSat(cmd)
                is Cmd.Reset -> reset(cmd)
                is Cmd.GetModel -> getModel(cmd)
                is Cmd.GetValue -> getValue(cmd)
                is Cmd.GetUnsatCore -> getUnsatCore(cmd)
                is Cmd.GetInfo -> getInfo(cmd)
                is Cmd.SetOption -> setOption(cmd)
                is Cmd.SetLogic -> setLogic(cmd)
                is Cmd.StatsCmd -> statsCmd(cmd)
                is Cmd.ResetAssertions -> resetAssertions(cmd)
                is Cmd.Push -> push(cmd)
                is Cmd.Pop -> pop(cmd)
            }
        }
    }

    open fun noopCmd(cmd: Cmd.NoOp) {
        /* do nothing */
    }

    open fun goalCmd(cmd: Cmd.Goal) {
        /* do nothing */
    }

    open fun modelCmd(cmd: Cmd.Model) {
        /* do nothing */
    }

    open fun assertCmd(cmd: Cmd.Assert) {
        expr(cmd.e)
    }

    open fun declareSort(cmd: Cmd.DeclareSort) {
        /* do nothing */
    }

    open fun declareDatatypes(cmd: Cmd.DeclareDatatypes) {
        /* do nothing */
    }

    open fun declareConst(cmd: Cmd.DeclareConst) {
        /* do nothing */
    }

    open fun declareFun(cmd: Cmd.DeclareFun) {
        /* do nothing */
    }

    open fun defineFun(cmd: Cmd.DefineFun) {
        if (inlineDefineFuns) {
            defineFuns.add(cmd)
        } else {
            expr(cmd.definition)
        }
    }

    open fun checkSat(cmd: Cmd.CheckSat) {
        /* do nothing */
    }

    open fun reset(cmd: Cmd.Reset) {
        /* do nothing */
    }

    open fun resetAssertions(cmd: Cmd.ResetAssertions) {
        /* do nothing */
    }

    open fun push(cmd: Cmd.Push) {
        /* do nothing */
    }

    open fun pop(cmd: Cmd.Pop) {
        /* do nothing */
    }

    open fun getModel(cmd: Cmd.GetModel) {
        /* do nothing */
    }

    open fun getValue(cmd: Cmd.GetValue) {
        /* do nothing */
    }

    open fun getUnsatCore(cmd: Cmd.GetUnsatCore) {
        /* do nothing */
    }

    open fun getInfo(cmd: Cmd.GetInfo) {
        /* do nothing */
    }

    open fun setOption(cmd: Cmd.SetOption) {
        /* do nothing */
    }

    open fun setLogic(cmd: Cmd.SetLogic) {
        /* do nothing */
    }

    open fun statsCmd(cmd: Cmd.StatsCmd) {
        /* do nothing */
    }

    open fun expr(exp: SmtExp) {
        if (!quit) {
            when (exp) {
                is SmtExp.QualIdentifier -> qualId(exp)
                is SmtExp.Apply -> apply(exp)
                is SmtExp.Lambda -> lambda(exp)
                is SmtExp.Let -> letExp(exp)
                is SmtExp.Quant -> quant(exp)
                is SmtExp.BitvectorLiteral -> bitVecLit(exp)
                is SmtExp.BoolLiteral -> boolLit(exp)
                is SmtExp.IntLiteral -> intLit(exp)
                is SmtExp.DecLiteral -> decLit(exp)
                is SmtExp.AnnotatedExp -> annotatedExp(exp)
                is SmtExp.PlaceHolder -> `impossible!`
            }
        }
    }

    open fun quant(exp: SmtExp.Quant) {
        when (exp) {
            is SmtExp.Quant.Exists -> existsExp(exp)
            is SmtExp.Quant.ForAll -> forallExp(exp)
        }
    }

    open fun qualId(exp: SmtExp.QualIdentifier) {
        /* do nothing */
    }

    open fun apply(exp: SmtExp.Apply) {
        if (inlineDefineFuns && exp.fs.name.sym in defineFuns.map { it.name }) {
            val definition = defineFuns.find { exp.fs.name.sym == it.name } as Cmd.DefineFun
            val inlined =
                Substitutor(definition.params.mapIndexed { i, sv -> sv.toQualId(script) to exp.args[i] }.toMap())
                    .expr(definition.definition, Unit)
            expr(inlined)
        } else {
            exp.args.forEach { expr(it) }
        }
    }

    open fun lambda(exp: SmtExp.Lambda) {
        throw UnsupportedOperationException("not implemented")
    }

    open fun letExp(exp: SmtExp.Let) {
        exp.defs.forEach { expr(it.def) }
        expr(exp.body)
    }

    open fun forallExp(exp: SmtExp.Quant.ForAll) {
        expr(exp.body)
    }

    open fun existsExp(exp: SmtExp.Quant.Exists) {
        expr(exp.body)
    }

    open fun bitVecLit(exp: SmtExp.BitvectorLiteral) {
        /* do nothing */
    }

    open fun boolLit(exp: SmtExp.BoolLiteral) {
        /* do nothing */
    }

    open fun intLit(exp: SmtExp.IntLiteral) {
        /* do nothing */
    }

    open fun decLit(exp: SmtExp.DecLiteral) {
        /* do nothing */
    }

    open fun annotatedExp(exp: SmtExp.AnnotatedExp) {
        expr(exp.innerExp)
    }
}
