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

package spec

import allocator.Allocator

/**
 * variable names/function names that we use internally -- we could/should/do avoid name clashes using this list
 *
 * TODO: how is this tied to CVL? apparently it's used in TAC as well? see, e.g. [toVar] method...
 */
enum class CVLReservedVariables {
    certoraArg,
    certoraArgLen,
    certoraArgTotalLen,
    certoraEqArgs,
    certoraParam,
    certoraEqParam,
    certoraTmp,
    certoraMaskedTmp,
    certoraInput,
    certoraTStrict,
    certoraTEq,
    certoraTPos,
    certoraOutVar,
    certoraMemOffset,

    certoraAssume,
    certoraAssert,
    certoraSatisfy,
    certoraResetStorage,
    certoraCond,
    certoraDummy,
    certoraDivisionByZero,
    certorafallback_0
    ;

    fun getUnique() = this.name + Allocator.getFreshNumber()

    companion object {
        const val prefix = "certora_"
        fun getWithReservedPrefix(name: String): String = "$prefix$name"
        const val certoraFallbackDisplayName: String = "<receiveOrFallback>"
    }

}
