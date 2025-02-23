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

package rules.genericrulecheckers.msgvalueinloop

import analysis.*
import analysis.CommandWithRequiredDecls.Companion.withDecls
import datastructures.stdcollections.*
import tac.Tag
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol
import vc.data.tacexprutil.TACExprFactSimple
import vc.data.tacexprutil.TACExprFreeVarsCollector

/**
 * Functions for generating vars for monitoring error in instrumentation.
 */
object ErrorCmdGenerator{

    fun createErrorVar(varName: String): TACSymbol.Var = TACSymbol.Var(varName, Tag.Bool)
    /**
     * The command added after each reference to msg.value inside a loop.
     * @return errorVar = errorVar LOR refExpr
     */
    fun errorVarUpdateCmd(
        errorVar: TACSymbol.Var,
        refExpr: TACExpr
    ): SimpleCmdsWithDecls {
        return listOf(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                errorVar, TACExprFactSimple.LOr(
                    listOf(errorVar.asSym(), refExpr),
                    Tag.Bool
                )
            )
        ).withDecls(errorVar)
    }

    /**
     * @return the expression \/_{v free in expr} refVar(v)
     * or of all refVar(v) for v that is free in expr.
     */
    fun freeVarsRefExpr(expr: TACExpr, varToRefVar: Map<TACSymbol.Var, TACSymbol.Var>): TACExpr {
        val freeVars = TACExprFreeVarsCollector.getFreeVars(expr)
        val refVars = varToRefVar.filterKeys { key -> key in freeVars }
        return if (refVars.values.isEmpty()) {
            TACExprFactSimple.False
        } else if (refVars.values.size == 1) {
            refVars.values.first().asSym()

        } else {
            TACExprFactSimple.LOr(refVars.values.map { v -> v.asSym() }, Tag.Bool)
        }
    }
}
