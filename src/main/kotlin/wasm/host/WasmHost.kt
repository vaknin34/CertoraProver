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

package wasm.host

import analysis.CommandWithRequiredDecls
import datastructures.stdcollections.*
import vc.data.*
import wasm.ir.*

// Represents a WASM host environment (e.g., Soroban)
interface WasmHost {
    fun init(): CommandWithRequiredDecls<TACCmd.Simple>
    fun importer(program: WasmProgram): Importer

    /** Host-specific transforms to be applied to the TAC prior to unrolling */
    fun applyPreUnrollTransforms(tac: CoreTACProgram.Linear, wasm: WasmProgram) = tac

    /** Host-specific optimizations to be applied after loop unrolling, before the general TAC optimizations */
    fun applyOptimizations(tac: CoreTACProgram.Linear, wasm: WasmProgram) = tac

    interface Importer {
        fun resolve(id: WasmName): Boolean

        fun importFunc(
            id: WasmName,
            args: List<TACSymbol>,
            retVar: TACSymbol.Var?
        ): CommandWithRequiredDecls<TACCmd.Simple>?
    }
}
