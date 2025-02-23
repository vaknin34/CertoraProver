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

package smtlibutils.cmdprocessor

import datastructures.stdcollections.*
import smtlibutils.data.*
import smtlibutils.statistics.QueryStatistics
import utils.*

/**
 * A collection of terms that we want to query the solver for model values for in case of a SAT result.
 *
 * [terms] is the collection of terms we will want a model value for
 * [backTranslation] allows the user to map the terms in [terms] back to some other representation (e.g. TACExpr)
 *
 * @param T the type that the backtranslation translates back to (this needs to be generic because e.g. TACExpr is not
 *   visible here in SMTLibUtils)
 */
open class TermsOfInterest(val terms: Set<SmtExp>) : Set<SmtExp> by terms {
    open fun copy(newTerms: Set<SmtExp>): TermsOfInterest = TermsOfInterest(newTerms)
}


/** Use if we want no values from the model in case of a SAT result. */
object EmptyTermsOfInterest: TermsOfInterest(emptySet())
/**
 * This contains all meta information about a checker query: name, configuration and statistics, but not the formula
 * itself.
 */
data class SmtFormulaCheckerQueryInfo(
    val name: String,
    val prettifyCounterExample: Boolean = false,
    val getUnsatCore: Boolean = false,
    val getDifficulties: Boolean = false,
    val learn: Boolean = false,
    val statistics: QueryStatistics = QueryStatistics(),
)

/**
 * @param termsOfInterest terms to query the solver for model values in case of a SAT result
 *
 */
data class SmtFormulaCheckerQuery(
    val info: SmtFormulaCheckerQueryInfo,
    val smtFormula: SmtFormula,
    val termsOfInterest: TermsOfInterest = EmptyTermsOfInterest,
    val coreHelper: CoreHelper? = null,
    val extras: List<HasSmtExp> = listOf(),
) {

    constructor(
        name: String,
        logic: Logic,
        symbolTable: SmtSymbolTable,
        defineFuns: List<Cmd.DefineFun>,
        declareDatatypes: List<Cmd.DeclareDatatypes>,
        formula: List<HasSmtExp>,
        termsForGetValue: TermsOfInterest = EmptyTermsOfInterest,
        coreHelper: CoreHelper? = null,
        prettifyCounterExample: Boolean = false,
        getUnsatCore: Boolean = false,
        getDifficulties: Boolean = false,
        learn: Boolean = false,
        statistics: QueryStatistics = QueryStatistics()
    ) : this(
        SmtFormulaCheckerQueryInfo(
            name,
            prettifyCounterExample,
            getUnsatCore,
            getDifficulties,
            learn,
            statistics,
        ),
        SmtFormula(logic, symbolTable, defineFuns, declareDatatypes, formula),
        termsForGetValue,
        coreHelper,
    )

    fun supplement(exps: List<HasSmtExp>) = copy(extras = extras + exps)
    fun supplement(exps: Sequence<HasSmtExp>) = copy(extras = (extras.asSequence() + exps).toList())

    init {
        check(!info.getUnsatCore || coreHelper != null)
        { "Illegal query: has `getUnsatCore` set to true, but no unsatCoreHelper ($this)." }
    }

    override fun toString(): String = "(SmtFormulaCheckerQuery, name: ${info.name}, logic: $logic)"

    val logic: Logic get() = smtFormula.logic
    val symbolTable: SmtSymbolTable get() = smtFormula.symbolTable
    val defineFuns: List<Cmd.DefineFun> get() = smtFormula.defineFuns
    val declareDatatypes: List<Cmd.DeclareDatatypes> get() = smtFormula.declareDatatypes

    fun formula(): List<HasSmtExp> = smtFormula.conjunction

    /**
     * TODO: unify with [CmdProcessor.assertCmds] (?)
     */
    fun assertFormulaSmtLines(script: ISmtScript) =
        sequence {
            yield(Cmd.NoOp("dumped from SmtFormulaCheckerQuery ${info.name}"))
            yield(script.setLogic(smtFormula.logic.toString()))
            yieldAll(declareDatatypes)

            symbolTable.getAllDeclaredSorts()
                // filter out the sorts that will be declared as part of a data type declaration
                .filter { declSort -> !declareDatatypes.any { ddt -> declSort.name.sym in ddt.sortDecNames } }
                .forEach { yield(it.toCommand(script)) }

            symbolTable.getAllDeclaredFuns()
                // filter out the functions that will be declared as part of a function definition or a datatype declaration
                .filter { declareFun ->
                    !defineFuns.any { defineFun -> defineFun.name == declareFun.id.sym } &&
                        !declareDatatypes
                            .any { ddt -> declareFun.id.sym in ddt.funDecNames }
                }.forEach { yield(it.toCommand(script)) }

            defineFuns.forEach {
                yield(it)
            }
            val f = (coreHelper?.getAnnotated()?.asSequence() ?: formula().asSequence()) + extras
            f.forEach {
                yield(script.assertCmd(it.exp).copy(comment = (it as? SmtExpWithComment)?.comment))
            }
        }

    /** Just the variables in the query */
    val variables by lazy {
        symbolTable.getAllDeclaredFuns()
            .filter { it.param_sorts.isEmpty() }
            .map { it.id }
            .filterIsInstance<Identifier.Simple>()
            .toSet()
    }

}
