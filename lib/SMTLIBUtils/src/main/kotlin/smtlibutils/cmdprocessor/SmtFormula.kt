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

import smtlibutils.algorithms.TraverseSmt
import smtlibutils.data.*

/**
 * Canonical form for "one formula" in SMT, including logic, necessary declarations, and definitions, in addition to
 * the formula itself.
 * (In contrast to [SMT], which represents a whole smt script, where multiple check-sats, push, pop, etc can happen.)
 */
data class SmtFormula(
    val logic: Logic,
    val symbolTable: SmtSymbolTable,
    val defineFuns: List<Cmd.DefineFun>,
    val declareDatatypes: List<Cmd.DeclareDatatypes>,
    val conjunction: List<HasSmtExp>,
) {
    /** for debugging; should be commented out in master */
    // val conjunctionPP = (conjunction() as Stream<HasSmtExp>).toArray()
    companion object {
        fun fromSmt(smt: SMT): SmtFormula {
            val logic = FindLogic.findLogic(smt)
            val symbolTable = run {
                val scriptWithSymbolTable = SmtScript()
                object : TraverseSmt() {
                    override fun declareConst(cmd: Cmd.DeclareConst) {
                        scriptWithSymbolTable.declareConst(cmd.name, cmd.sort)
                        super.declareConst(cmd)
                    }

                    override fun declareFun(cmd: Cmd.DeclareFun) {
                        scriptWithSymbolTable.declareFun(cmd.name, cmd.param_sorts, cmd.result_sort)
                        super.declareFun(cmd)
                    }

                    override fun declareSort(cmd: Cmd.DeclareSort) {
                        scriptWithSymbolTable.declareSort(cmd.sortDec)
                        super.declareSort(cmd)
                    }

                    override fun defineFun(cmd: Cmd.DefineFun) {
                        scriptWithSymbolTable.defineFun(cmd.name, cmd.params, cmd.res_sort, cmd.definition)
                        super.defineFun(cmd)
                    }

                    override fun declareDatatypes(cmd: Cmd.DeclareDatatypes) {
                        scriptWithSymbolTable.declareDatatypes(cmd.sortDecs, cmd.constructorDecListList)
                        super.declareDatatypes(cmd)
                    }
                }.smt(smt)
                scriptWithSymbolTable.symbolTable
            }
            if (smt.cmds.any {
                    it is Cmd.Push ||
                            it is Cmd.Pop ||
                            it is Cmd.Model ||
                            it is Cmd.Reset ||
                            it is Cmd.Goal
                }) {
                throw UnsupportedOperationException("cannot convert Smt object to (a single) formula, forbidden command")
            }
            val defineFuns = smt.cmds.filterIsInstance<Cmd.DefineFun>()
            val declareDatatypes = smt.cmds.filterIsInstance<Cmd.DeclareDatatypes>()
            val formula = smt.cmds.mapNotNull { if (it is Cmd.Assert) it.e else null }
            return SmtFormula(logic, symbolTable, defineFuns, declareDatatypes, formula)
        }
    }
}
