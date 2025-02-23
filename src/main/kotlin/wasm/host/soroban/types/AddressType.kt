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

import datastructures.stdcollections.*
import analysis.CommandWithRequiredDecls.Companion.mergeMany
import com.certora.collect.*
import utils.*
import vc.data.*
import wasm.host.soroban.*
import wasm.tacutils.*
import wasm.traps.*

@Treapable
@KSerializable
object AddressType : ObjectType() {
    override fun hashCode() = hashObject(this)

    override val tag = Val.Tag.AddressObject

    override fun init() = mergeMany(
        super.init(),
        assignHavoc(TACKeyword.SOROBAN_ADDRESS_AUTH.toVar()),
        assignHavoc(TACKeyword.SOROBAN_ADDRESS_TO_STRKEY.toVar()),
    )

    fun new(newHandle: TACSymbol.Var) =
        mergeMany(
            allocHandle(newHandle) {
                // Addresses have "reference equality" semantics; we simply use the handle value as the content digest.
                listOf(newHandle.asSym())
            }
        )

    fun isAuth(dest: TACSymbol.Var, handle: TACSymbol) =
        Val.withDigest(handle.asSym()) { digest ->
            assign(dest) {
                select(TACKeyword.SOROBAN_ADDRESS_AUTH.toVar().asSym(), digest)
            }
        }

    fun requireAuth(handle: TACSymbol) =
        Val.withDigest(handle.asSym()) { digest ->
            Trap.assert("not authorized") {
                select(TACKeyword.SOROBAN_ADDRESS_AUTH.toVar().asSym(), digest)
            }
        }

    fun toStrKey(dest: TACSymbol.Var, handle: TACSymbol) =
        Val.withDigest(handle.asSym()) { addressDigest ->
            assign(dest) {
                select(TACKeyword.SOROBAN_ADDRESS_TO_STRKEY.toVar().asSym(), addressDigest)
            }
        }
}
