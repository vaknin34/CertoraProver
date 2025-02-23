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

package wasm.host.soroban.types

import analysis.CommandWithRequiredDecls
import com.certora.collect.*
import datastructures.stdcollections.*
import tac.*
import utils.*
import vc.data.*
import wasm.host.soroban.*

/**
    Implementats common object functionality

    All objects are represented by [Val] handles with a particular tag, given by [tag].  [fresh] is a TAC variable
    used to allocate new handles (by incrementing it for each allocation).
*/
@Treapable
@KSerializable
abstract class ObjectType : HasKSerializable {
    abstract val tag: Val.Tag

    /**
        Initializes the global state associated with this object type in the TAC.
     */
    open fun init() = CommandWithRequiredDecls<TACCmd.Simple>()

    /**
        Allocates a new handle of this type.
     */
    fun allocHandle(dest: TACSymbol.Var, contentSummary: (TACExprFact.() -> List<TACExpr>)? = null) =
        Val.allocHandle(dest, tag, contentSummary)
}
