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

import wasm.tokens.WasmTokens
import java.io.Serializable
import java.math.BigInteger

enum class WasmPrimitiveType : Serializable {
    I32 {
        override val initializer: WasmInstruction
            get() = WasmInstruction.Numeric.I32Const(I32Value(BigInteger.ZERO))

        override fun toString(): String {
            return WasmTokens.I32
        }
    },
    I64 {
        override val initializer: WasmInstruction
            get() = WasmInstruction.Numeric.I64Const(I64Value(BigInteger.ZERO))

        override fun toString(): String {
            return WasmTokens.I64
        }
    },
    F32 {
        override val initializer: WasmInstruction
            get() = WasmInstruction.Numeric.F32Const(F32Value(0F))

        override fun toString(): String {
            return WasmTokens.F32
        }
    },
    F64 {
        override val initializer: WasmInstruction
            get() = WasmInstruction.Numeric.F64Const(F64Value(0.0))

        override fun toString(): String {
            return WasmTokens.F64
        }
    };

    abstract val initializer: WasmInstruction

    companion object {
        val BOOL = I32
    }
}

enum class WasmMutability : Serializable {
    MUT {
        override fun toString(): String {
            return WasmTokens.MUT
        }
    }
}
