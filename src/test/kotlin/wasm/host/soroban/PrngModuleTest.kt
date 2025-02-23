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

package wasm.host.soroban

import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.*
import wasm.*
import wasm.host.soroban.SorobanImport.Buf
import wasm.host.soroban.SorobanImport.Prng
import wasm.host.soroban.SorobanImport.Vec
import wasm.host.soroban.Val.Tag.*
import wasm.wat.*

class PrngModuleTest : SorobanTestFixture() {
    @Test
    fun prng_reseed() {
        assertTrue(verifyWasm {
            val obj = Prng.bytesNew(U32Val(32))
            certoraAssert(Prng.reseed(obj) eq VoidVal)
        })
    }

    @Test
    fun prng_bytes_new() {
        assertTrue(verifyWasm {
            certoraAssert(Buf.len(Prng.bytesNew(U32Val(888))) eq U32Val(888))
        })
    }

    @Test
    fun prng_u64_in_inclusive_range() {
        assertTrue(verifyWasm {
            val result = Prng.u64InInclusiveRange(i64(1234), i64(5678))
            certoraAssert((i64(1234) le result) and (result le i64(5678)))
        })
    }

    @Test
    fun prng_vec_shuffle() {
        assertTrue(verifyWasm {
            val obj = (1..5).fold(Vec.new()) { acc, i -> Vec.push_back(acc, I32Val(i)) }
            Prng.vecShuffle(obj)
            certoraAssert(Vec.len(obj) eq U32Val(5))
        })
    }
}
