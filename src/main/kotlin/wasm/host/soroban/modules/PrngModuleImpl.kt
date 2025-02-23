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

import analysis.CommandWithRequiredDecls.Companion.mergeMany
import datastructures.stdcollections.*
import utils.*
import vc.data.*
import wasm.host.soroban.*
import wasm.host.soroban.types.*
import wasm.tacutils.*
import wasm.traps.*

internal object PrngModuleImpl : ModuleImpl() {
    override fun getFuncImpl(funcName: String, args: List<TACSymbol>, retVar: TACSymbol.Var?) =
        when(funcName) {
            "prng_reseed" -> reseed(args[0])
            "prng_bytes_new" -> bytesNew(args[0], retVar!!)
            "prng_u64_in_inclusive_range" -> u64InInclusiveRange(args[0], args[1], retVar!!)
            "prng_vec_shuffle" -> vecShuffle(args[0], retVar!!)
            else -> null
        }

    private fun reseed(seed: TACSymbol) =
        // Just validate the seed length.  We don't actually use it.
        BytesType.withSize(seed) {
            Trap.assert("Seed must be 32 bytes long.") { it.asSym() eq 32.asTACExpr }
        }

    private fun bytesNew(length: TACSymbol, retVar: TACSymbol.Var) =
        // Produce a buffer of the given length, with indeterminite contents.
        BytesType.new(retVar) { length.asSym() }

    private fun u64InInclusiveRange(lo: TACSymbol, hi: TACSymbol, retVar: TACSymbol.Var) =
        // Produce an indeterminite value in the range [lo, hi].
        mergeMany(
            assignHavoc(retVar),
            assume { (lo.asSym() le retVar.asSym()) and (retVar.asSym() le hi.asSym()) }
        )

    private fun vecShuffle(vec: TACSymbol, retVar: TACSymbol.Var) =
        // Produce a vector of the same size as [vec], and indeterminate contents
        VecType.withSize(vec) { size ->
            VecType.new(retVar) { size.asSym() }
        }
}
