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


/**
    Implements CVT helper functions for rules targeting Soroban.  These are extra functions that aren't part of the
    Soroban API, but are useful for writing rules.
 */
internal object CvtEnvModuleImpl : ModuleImpl() {

    private enum class Function(val ret: SorobanType, vararg val args: Pair<String, SorobanType>) {
        IS_AUTH(SorobanType.Bool, "address" to SorobanType.AddressObject)
    }

    val module = SorobanModule(
        export = "env",
        name = "env",
        functions = Function.entries.map { func ->
            SorobanFunction(
                export = "CERTORA_SOROBAN_" + func.name.lowercase(),
                name = func.name,
                args = func.args.map { (name, type) -> SorobanArg(name, type) },
                ret = func.ret
            )
        }
    )

    override fun getFuncImpl(funcName: String, args: List<TACSymbol>, retVar: TACSymbol.Var?) =
        when (Function.valueOf(funcName)) {
            Function.IS_AUTH -> AddressType.isAuth(retVar!!, args[0])
        }
}
