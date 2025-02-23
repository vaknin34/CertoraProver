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

internal object LedgerModuleImpl : ModuleImpl() {
    override fun getFuncImpl(funcName: String, args: List<TACSymbol>, retVar: TACSymbol.Var?) =
        when(funcName) {
            "put_contract_data" -> Contract.putContractData(args[0], args[1], args[2])
            "has_contract_data" -> Contract.hasContractData(retVar!!, args[0], args[1])
            "get_contract_data" -> Contract.getContractData(retVar!!, args[0], args[1])
            "del_contract_data" -> Contract.deleteContractData(args[0], args[1])
            // TODO CERT-6459 CERT-6457
            else -> null
        }
}
