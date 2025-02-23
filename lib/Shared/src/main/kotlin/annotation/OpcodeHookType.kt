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

package annotation

import kotlin.reflect.KClass

@Target(AnnotationTarget.FIELD)
annotation class OpcodeHookType(
    val params : Array<String> = [],
    val withOutput: Boolean,
    // ignored if withOutput == false
    val valueType: String = "uint256",
    val onlyNoStorageSplitting: Boolean = false,
    /*
      Parameters that are part of the "environment" of the executing opcode. The executingContractVar
      fulfills this role, but because that is *always* bound, we special case it instead of requiring adding
      it everywhere.

      No relation to the `env` CVL type.
     */
    val envParams : Array<String> = [],

    val extraInterfaces: Array<KClass<*>> = []
)
