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
import smtlibutils.parser.SmtSymbolQuoter.quoteIfNecessary

sealed class Cmd {

    /**
     * Indicates whether we expect any output from the solver after issuing this command. Be careful setting this to
     * true! Setting it to false incorrectly merely delays reading the output such that a potential warning or error is
     * only picked up by a later command. Setting it to true incorrectly, though, may stall the solving as we block and
     * wait for solver output that will not come.
     * If you have any doubt, keep [false].
     */
    open val expectsResult: Boolean = false

    open val comment: String? = null

    protected fun withComment(cmd: String): String {
        return if (comment == null) cmd
        else "$cmd ; $comment"
    }

    /**
     * For commands that we don't have in this [Cmd] AST but want to use.
     * Any further processing won't work on these commands.
     * Make sure to not use this for any of the known commands.
     */
    data class Custom(val s: String, override val expectsResult: Boolean = false, override val comment: String? = null) : Cmd() {

        init {
            /* some checks to avoid misusing this class -- could be made nicer ... (maybe a fromString for Commands?) */
            check(s != "(reset)") { "use designated reset() command for this" }
            check(s != "(check-sat)") { "use designated checkSat() command for this" }
            check(!s.startsWith("(set-logic")) { "use designated setLogic() command for this" }
        }

        override fun toString() = withComment(s)
    }

    data class NoOp(override val comment: String? = null): Cmd() {
        override fun toString() = withComment("")
    }

    data class Goal(val exprs: List<SmtExp>) : Cmd() {
        override fun toString(): String {
            return withComment("(goal \n ${exprs.joinToString("\n")}\n)")
        }
    }

    data class Model(val defs: List<Cmd>) : Cmd() {
        override fun toString(): String {
            return withComment(defs.joinToString("\n"))
        }
    }

    /**
     * A list of value definitions -- as returned by [GetValue] command.
     */
    data class ValDefList(val valDefs: List<ValDef>) : Cmd() {
        override fun toString() = withComment("(${valDefs.joinToString(" ")})")
    }

    data class Assert(val e: SmtExp, override val comment: String? = null) : Cmd(), HasSmtExp {
        override val exp: SmtExp
            get() = e

        override fun mapExp(mapper: (SmtExp) -> SmtExp): HasSmtExp = this.copy(e = mapper(e))

        override fun toString() = withComment("($keyword $e)")

        companion object {
            const val keyword = "assert"
        }
    }

    data class DeclareSort(val sortDec: SortDec, override val comment: String? = null) : Cmd() {
        val name: String get() = sortDec.name
        val arity: Int get() = sortDec.arity

        override fun toString() = withComment("(declare-sort $sortDec)")
    }

    data class DeclareDatatypes(
        val sortDecs: List<SortDec>,
        val constructorDecListList: List<List<DatatypeConstructorDec>>,
        override val comment: String? = null,
    ) : Cmd() {
        val sortDecNames: Set<String> = sortDecs.mapTo(datastructures.stdcollections.mutableSetOf()) { it.name }
        val funDecNames: Set<String> =
            constructorDecListList.flatMapTo(datastructures.stdcollections.mutableSetOf()) { cdList ->
                cdList.flatMap { cd -> cd.selectors.map { it.id } + datastructures.stdcollections.listOf(cd.name) }
            }

        override fun toString(): String {
            return withComment("(declare-datatypes ${sortDecs.joinToString(" ", "(", ")") { "($it)" }} " +
                    constructorDecListList.joinToString(" ", "(", ")")
                    { it.joinToString(" ", "(", ")") } +
                    ")")
        }
    }

    data class DeclareConst(val name: String, val sort: Sort,
                            override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(declare-const ${quoteIfNecessary(name)} $sort)")
    }

    data class DeclareFun(val name: String, val param_sorts: List<Sort>, val result_sort: Sort,
                          override val comment: String? = null) : Cmd() {
        override fun toString(): String {
            return withComment("(declare-fun ${quoteIfNecessary(name)} (${param_sorts.joinToString(" ")}) $result_sort)")
        }
    }

    data class DefineFun(
        val name: String,
        val params: List<SortedVar>,
        val res_sort: Sort,
        val definition: SmtExp,
        override val comment: String? = null,
    ) : Cmd() {
        val rank = Rank(params.map { it.sort }, res_sort)
        val rankWithNamedParams = RankWithNamedParams(rank, params.map { it.id })

        override fun toString(): String {
            return withComment("($keyword $name (${params.joinToString(" ")}) $res_sort $definition)")
        }

        companion object {
            const val keyword = "define-fun"
        }
    }

    data class Reset(override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(reset)")
    }

    data class ResetAssertions(override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(reset-assertions)")
    }

    data class CheckSat(override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(check-sat)")

        override val expectsResult: Boolean = true
    }

    data class GetModel(override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(get-model)")

        override val expectsResult: Boolean = true
    }

    data class GetValue(val expList: List<SmtExp>, override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(get-value (${expList.joinToString(" ")}))")

        override val expectsResult: Boolean = true
    }

    data class GetInfo(val name: String, override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(get-info $name)")

        override val expectsResult: Boolean = true
    }

    data class GetUnsatCore(override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(get-unsat-core)")

        override val expectsResult: Boolean = true
    }

    data class SetOption(val name: String, val value: String, override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(set-option $name $value)")
    }

    data class SetLogic(val logic: String, override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(set-logic $logic)")
    }

    data class StatsCmd(val stats: List<Stat>, override val comment: String? = null) : Cmd() {
        override fun toString(): String {
            return withComment("(${stats.map { "${it.statName}                  ${it.value}" }.joinToString(" ")})")
        }
    }

    data class Push(val n: Int, override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(push $n)")
    }

    data class Pop(val n: Int, override val comment: String? = null) : Cmd() {
        override fun toString() = withComment("(pop $n)")
    }
}
