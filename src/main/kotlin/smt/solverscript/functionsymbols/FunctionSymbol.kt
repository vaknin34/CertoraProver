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

package smt.solverscript.functionsymbols

import com.certora.collect.*
import smtlibutils.data.ISmtScript
import smtlibutils.data.SmtFunctionSymbol
import tac.Tag
import utils.AmbiSerializable
import vc.data.ToSmtLibData
import vc.data.lexpression.getResultOfSignature

/**
 *
 * @param name this is how the function will be printed in the smt file or be v
 * @param lExpressionConstructor Constructs an [LExpression] from a list of arguments (legacy, until we have simplified
 *  the AST as described above. We should be able to deprecate this field once LExpression is changed to the new style
 *  AST.)'
 *
 *
 * Note: this could be a sealed class { [InterpretedFunctionSymbol], [UninterpretedFunctionSymbol] }, but then all
 *   subclasses would have to be in one file, apparently
 *
 */
@utils.KSerializable
@Treapable
sealed class FunctionSymbol: AmbiSerializable {

    abstract val name: String
    abstract val signature: FunctionSignature
    open fun getResultTag(args: List<Tag>): Tag = getResultOfSignature(signature, args)

    override fun toString(): String = name

    abstract fun toSMTLib(toSmtLibData: ToSmtLibData, script: ISmtScript): SmtFunctionSymbol
}

/**
 * Note: this could be a sealed class, but then all subclasses would have to be in one file, apparently
 */
@utils.KSerializable
abstract class InterpretedFunctionSymbol : FunctionSymbol()
