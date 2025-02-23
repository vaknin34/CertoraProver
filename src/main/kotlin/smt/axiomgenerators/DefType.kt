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

package smt.axiomgenerators

import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.FunctionSymbol
import smtlibutils.data.Cmd
import smtlibutils.data.ISmtScript
import tac.Tag
import vc.data.LExpression
import vc.data.ToSmtLibData

/**
 * The LExpression-equivalent to SMT's define-fun
 */
data class DefType(
    val id: FunctionSymbol,
    val args: List<LExpression.Identifier>,
    val ret: Tag,
    val def: LExpression,
    val comment : String? = null) {

    // TODO: nothing is done with the comment. Should really propagate down to the smt file.
    /**
     * Allows postprocessing, e.g. when the define-fun has some function symbol that requires theory-specific
     * normalization, like `IntAdd` becoming `BvAdd` for bv logics.
     */
    fun process(transform: (LExpression) -> LExpression): DefType {
        return this.copy(
            // args = this.args.map { (id, tag) -> transform(id) as LExpression.Identifier to tag }, // --> unclear if this makes sense
            def = transform(this.def)
        )
    }

    fun toSmtLib(toSmtLibData: ToSmtLibData, scriptWithSymbolTable: ISmtScript): Cmd.DefineFun {
        return scriptWithSymbolTable.defineFun(
            id.toSMTLib(toSmtLibData, scriptWithSymbolTable).toSMTLIBString(),
            args.map { arg ->
                scriptWithSymbolTable.sortedVar(
                    arg.id,
                    LExpressionFactory.tagToSort(arg.tag, toSmtLibData)
                )
            },
            LExpressionFactory.tagToSort(ret, toSmtLibData),
            def.toSMTLib(toSmtLibData, scriptWithSymbolTable)
        )
    }
}



