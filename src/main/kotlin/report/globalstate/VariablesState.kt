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

package report.globalstate

import datastructures.stdcollections.*
import report.calltrace.CallTrace
import report.calltrace.formatter.FormatterType.Companion.toFormatterType
import report.calltrace.sarif.Sarif
import solver.CounterexampleModel
import vc.data.*

/**
 * A unit of the [CallTrace]. Represents the variables during the flow of the CounterExample TACProgram chosen by the SMT.
 */
internal class VariablesState(private val model: CounterexampleModel) {
    private val variableMap: MutableMap<TACSymbol.Var, DisplaySymbolWrapper> = mutableMapOf()

    fun computationalTypeForRHS(rhs: Set<TACSymbol.Var>) : ComputationalTypes = rhs.fold(ComputationalTypes.CONCRETE) { ret, symbol ->
        when(variableMap[symbol]?.computationalType) {
            null, ComputationalTypes.UNKNOWN -> { return ComputationalTypes.UNKNOWN }
            ComputationalTypes.DONT_CARE -> { throw IllegalStateException("Usage of DONT CARE symbol $symbol") }
            ComputationalTypes.HAVOC, ComputationalTypes.HAVOC_DEPENDENT -> { return@fold ComputationalTypes.HAVOC_DEPENDENT }
            ComputationalTypes.CONCRETE -> { return@fold ret }
        }
    }

    fun computationalTypeForRHS(rhs: TACSymbol.Var) = computationalTypeForRHS(setOf(rhs))

    private fun computationalTypeForTACCommand(assign: TACCmd.Simple.AssigningCmd) = when(assign) {
        is TACCmd.Simple.AssigningCmd.AssignHavocCmd -> ComputationalTypes.HAVOC
        is TACCmd.Simple.AssigningCmd.AssignExpCmd -> computationalTypeForRHS(assign.getFreeVarsOfRhs())
        else -> ComputationalTypes.UNKNOWN
    }

    fun handleAssignments(stmt: TACCmd.Simple.AssigningCmd) {
        val value = model.valueAsTACValue(stmt.lhs)
        val computationalType = computationalTypeForTACCommand(stmt)

        val formatterType =
            stmt.lhs.meta.find(TACMeta.CVL_TYPE)
            ?.toFormatterType()

        val range = stmt.metaSrcInfo?.getSourceDetails()?.range

        variableMap[stmt.lhs] = DisplaySymbolWrapper(
            Sarif.fromPlainStringUnchecked(stmt.lhs.namePrefix),
            value,
            computationalType,
            formatterType,
            range
        )
    }

    operator fun set(sym: TACSymbol.Var, dsw: DisplaySymbolWrapper) {
        variableMap[sym] = dsw
    }

    operator fun get(sym: TACSymbol.Var) = variableMap[sym]
}
