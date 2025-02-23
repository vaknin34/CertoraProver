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

internal object MapModuleImpl : ModuleImpl() {
    override fun getFuncImpl(funcName: String, args: List<TACSymbol>, retVar: TACSymbol.Var?) =
        when(funcName) {
            "map_new" -> MapType.empty(retVar!!)
            "map_put" -> MapType.put(retVar!!, args[0], args[1], args[2])
            "map_get" -> MapType.get(retVar!!, args[0], args[1])
            "map_del" -> MapType.delete(retVar!!, args[0], args[1])
            "map_len" -> MapType.getSize(retVar!!, args[0])
            "map_has" -> MapType.contains(retVar!!, args[0], args[1])
            "map_key_by_pos" -> MapType.getKeyByIndex(retVar!!, args[0], args[1])
            "map_val_by_pos" -> MapType.getValueByIndex(retVar!!, args[0], args[1])
            "map_keys" -> MapType.getKeys(retVar!!, args[0])
            "map_values" -> MapType.getValues(retVar!!, args[0])
            "map_new_from_linear_memory" -> MapType.newFromMemory(retVar!!, args[0], args[1], args[2])
            "map_unpack_to_linear_memory" -> MapType.unpackToMemory(args[0], args[1], args[2], args[3])
            else -> null
        }
}
