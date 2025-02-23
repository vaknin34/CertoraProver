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

package wasm.ir

import java.io.Serializable
import java.math.BigInteger

interface WasmSymbol: Serializable {
    override fun toString(): String
}

interface WasmConst: WasmSymbol

data class I32Value(val v: BigInteger): WasmConst {
    override fun toString(): String {
        return v.toString()
    }
}

data class I64Value(val v: BigInteger): WasmConst {
    override fun toString(): String {
        return v.toString()
    }
}

data class F32Value(val v: Float): WasmConst {
    override fun toString(): String {
        return v.toString()
    }
}

data class F64Value(val v: Double): WasmConst {
    override fun toString(): String {
        return v.toString()
    }
}

data class Variable(val s: String): WasmSymbol {
    override fun toString(): String {
        return s
    }
}
