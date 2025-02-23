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

package vc.data.lexpression

import smt.solverscript.functionsymbols.FunctionSignature
import smt.solverscript.functionsymbols.NrOfParameters
import tac.*
import utils.*
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

class LExpressionTypeException(msg: String, cause: Throwable? = null):
    CertoraInternalException(CertoraInternalErrorType.LEXPRESSION_TYPING, msg, cause)

@OptIn(ExperimentalContracts::class)
inline fun checkTyping(value: Boolean, lazyMessage: () -> Any) {
    contract {
        returns() implies value
    }
    if (!value) {
        val message = lazyMessage()
        throw LExpressionTypeException(message.toString())
    }
}

fun getResultOfSignature(signature: FunctionSignature, args: List<Tag>): Tag {
    when (val nrOf = signature.nrOfParameters) {
        is NrOfParameters.Fixed -> checkTyping(args.size == nrOf.n) {
            "Expected ${nrOf.n} arguments but got ${args.size}"
        }
        is NrOfParameters.Flexible -> checkTyping(args.size >= nrOf.minParamCount) {
            "Expected at least ${nrOf.minParamCount} arguments but got ${args.size}"
        }
    }
    args.forEachIndexed { index, tag ->
        checkTyping(tag.isSubtypeOf(signature.getParamSort(index)!!)) {
            "Expected argument #${index + 1} to be ${signature.getParamSort(index)} but got $tag"
        }
    }
    return signature.resultSort
}

