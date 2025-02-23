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

package wasm.summarization.soroban

import datastructures.stdcollections.*
import analysis.CommandWithRequiredDecls
import tac.Tag
import utils.*
import vc.data.TACCmd
import vc.data.TACSymbol
import wasm.host.soroban.types.SymbolType
import wasm.impCfg.*
import wasm.ir.WasmName
import wasm.ir.WasmPrimitiveType
import wasm.ir.WasmProgram.*
import wasm.summarization.WasmCallSummarizer

/**
 * A summarizer for Soroban SDK functions
 */
class SorobanSDKSummarizer(
    private val typeContext: Map<WasmName, WasmFuncDesc>,
): WasmCallSummarizer {

    /**
     * Soroban SDK functions we can summarize
     *
     * @param demangledName the demangled name of the function
     * @param params the expected parameter types of the builtin
     * @param ret the expected return type
     */
    enum class SorobanSDKBuiltin(val demangledName: String, val params: List<WasmPrimitiveType>, val ret: WasmPrimitiveType?) {
        SYMBOL_NEW("\$soroban_sdk::symbol::Symbol::new",
            listOf(WasmPrimitiveType.I32, WasmPrimitiveType.I32),
            WasmPrimitiveType.I64
        ),

        SYMBOL_TRY_FROM_VAL_STRREF(
            "\$<soroban_env_common::symbol::Symbol as soroban_env_common::convert::TryFromVal<E,&str>>::try_from_val",
            listOf(WasmPrimitiveType.I32, WasmPrimitiveType.I32),
            WasmPrimitiveType.I64
            )
        ;
    }

    override fun canSummarize(f: WasmName): Boolean = asSDKFunc(f) != null

    private fun asSDKFunc(f: WasmName): SorobanSDKBuiltin? {
        return when (val tyDesc = typeContext[f]) {
            is WasmFuncDesc.LocalFn -> {
                val demangledName = WasmInliner.demangle(f.toString())
                SorobanSDKBuiltin.values().singleOrNull() {
                    demangledName == it.demangledName &&
                        tyDesc.fnType.params == it.params &&
                        tyDesc.fnType.result == it.ret
                }
            }
            else -> null
        }
    }

    context(WasmImpCfgContext) override fun summarizeCall(call: StraightLine.Call): CommandWithRequiredDecls<TACCmd.Simple> {
        return when (asSDKFunc(call.id)) {
            SorobanSDKBuiltin.SYMBOL_TRY_FROM_VAL_STRREF,
            SorobanSDKBuiltin.SYMBOL_NEW -> {
                check(call.maybeRet != null) { "expected Symbol::new to have an lhs" }
                summarizeSymbolNew(call.maybeRet, call.args[0], call.args[1])
            }

            else ->
                throw UnknownSorobanSDKFunction(call.id)
        }
    }

    private fun summarizeSymbolNew(lhs: Tmp, strPtr: Arg, len: Arg) =
        SymbolType.newFromStr(
            TACSymbol.Var(lhs.toString(), Tag.Bit256),
            strPtr.toTacSymbol(),
            len.toTacSymbol()
        )
}

class UnknownSorobanSDKFunction(val f: WasmName): Exception()
