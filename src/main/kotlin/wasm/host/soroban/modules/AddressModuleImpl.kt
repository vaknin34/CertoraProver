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

package wasm.host.soroban.modules

import vc.data.*
import wasm.host.soroban.*
import wasm.host.soroban.types.*

internal object AddressModuleImpl : ModuleImpl() {
    override fun getFuncImpl(funcName: String, args: List<TACSymbol>, retVar: TACSymbol.Var?) =
        when(funcName) {
            "require_auth" -> AddressType.requireAuth(args[0])

            // TODO: https://certora.atlassian.net/browse/CERT-6440
            "require_auth_for_args" -> null
            "strkey_to_address" -> null
            "address_to_strkey" -> AddressType.toStrKey(retVar!!, args[0])
            "authorize_as_curr_contract" -> null

            else -> null
        }
}
