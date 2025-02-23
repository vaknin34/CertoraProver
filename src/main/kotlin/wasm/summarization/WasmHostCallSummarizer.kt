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

package wasm.summarization

import analysis.CommandWithRequiredDecls
import tac.Tag
import vc.data.TACCmd
import vc.data.TACSymbol
import wasm.host.WasmHost
import wasm.impCfg.StraightLine
import wasm.impCfg.WasmImpCfgContext
import wasm.ir.WasmName

class WasmHostCallSummarizer(
    private val importer: WasmHost.Importer
): WasmCallSummarizer {
    override fun canSummarize(f: WasmName): Boolean = importer.resolve(f)

    context(WasmImpCfgContext) override fun summarizeCall(call: StraightLine.Call): CommandWithRequiredDecls<TACCmd.Simple> {
        val retVar = call.maybeRet?.let { TACSymbol.Var(it.toString(), Tag.Bit256) }
        val argSyms = call.args.map { it.toTacSymbol() }
        val fn = importer.importFunc(call.id, argSyms, retVar)
        check (fn != null) { "tried to import an unresolvable fn: ${call}"}
        return fn
    }
}
