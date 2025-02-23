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

package wasm.impCfg

import datastructures.stdcollections.*
import wasm.cfg.PC
import wasm.ir.WasmPrimitiveType
import wasm.tokens.WasmTokens.TMP
import wasm.tokens.WasmTokens.UNDERSCORE

/**
 * Tmp is used to make new registers as we need them.
 * */
data class Tmp(val type: WasmPrimitiveType, val pc: PC, val name: String, val callIdx: Int) {
    override fun toString(): String {
        return if (name.isNotEmpty()) {
            listOf(TMP, pc.toString(), name, callIdx).joinToString(UNDERSCORE)
        } else {
            listOf(TMP, pc.toString(), callIdx).joinToString(UNDERSCORE)
        }
    }
}


