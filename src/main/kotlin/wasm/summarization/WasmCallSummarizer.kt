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
import vc.data.TACCmd
import wasm.impCfg.StraightLine
import wasm.impCfg.WasmImpCfgContext
import wasm.ir.WasmName

/** Something that knows how to convert a particular call to TAC (presumably without inlining) */
interface WasmCallSummarizer {
    /** Whether this knows how to replace calls to [f] */
    fun canSummarize(f: WasmName): Boolean

    /**
     * Convert [call] to TAC.
     * @pre canSummarize([call.id]) == true
     */
    context (WasmImpCfgContext)
    fun summarizeCall(call: StraightLine.Call): CommandWithRequiredDecls<TACCmd.Simple>
}

/** Build a new [WasmCallSummarizer] that tries the summarizers in [summarizers] in order */
fun summarizers(summarizers: List<WasmCallSummarizer>): WasmCallSummarizer = object : WasmCallSummarizer {
    fun findSummarizerForFn(f: WasmName): WasmCallSummarizer? =
        summarizers.firstOrNull() {
            it.canSummarize(f)
        }

    override fun canSummarize(f: WasmName): Boolean =
        findSummarizerForFn(f) != null

    context(WasmImpCfgContext) override fun summarizeCall(call: StraightLine.Call): CommandWithRequiredDecls<TACCmd.Simple> {
        val summarizer = findSummarizerForFn(call.id)
        check(summarizer != null) { "Attempting to summarize an un-summarizable call $call"}
        return summarizer.summarizeCall(call)
    }
}
