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
import wasm.host.soroban.SorobanImport.Vec
import wasm.host.soroban.Val.Tag.*
import wasm.wat.*

class VecModuleTest : SorobanTestFixture() {
    @Test
    fun new() {
        assertTrue(verifyWasm {
            val vec = Vec.new()
            certoraAssert(Vec.len(vec) eq U32Val(0))
        })
    }

    @Test
    fun push_back() {
        assertTrue(verifyWasm {
            val zeroElems = Vec.new()

            // Push one elem and verifty that it worked
            val oneElem = Vec.push_back(zeroElems, U32Val(42))
            certoraAssert(Vec.len(oneElem) eq U32Val(1))
            certoraAssert(Vec.get(oneElem, U32Val(0)) eq U32Val(42))
            certoraAssert(Vec.front(oneElem) eq U32Val(42))
            certoraAssert(Vec.back(oneElem) eq U32Val(42))

            // Push another elem
            val twoElems = Vec.push_back(oneElem, U32Val(43))
            certoraAssert(Vec.len(twoElems) eq U32Val(2))
            certoraAssert(Vec.get(twoElems, U32Val(0)) eq U32Val(42))
            certoraAssert(Vec.get(twoElems, U32Val(1)) eq U32Val(43))
            certoraAssert(Vec.front(twoElems) eq U32Val(42))
            certoraAssert(Vec.back(twoElems) eq U32Val(43))

            // Check that oneElem was not affected
            certoraAssert(Vec.len(oneElem) eq U32Val(1))
            certoraAssert(Vec.get(oneElem, U32Val(0)) eq U32Val(42))
            certoraAssert(Vec.front(oneElem) eq U32Val(42))
            certoraAssert(Vec.back(oneElem) eq U32Val(42))
        })
    }

    @Test
    fun push_front() {
        assertTrue(verifyWasm {
            val zeroElems = Vec.new()

            // Push one elem and verifty that it worked
            val oneElem = Vec.push_front(zeroElems, U32Val(42))
            certoraAssert(Vec.len(oneElem) eq U32Val(1))
            certoraAssert(Vec.get(oneElem, U32Val(0)) eq U32Val(42))
            certoraAssert(Vec.front(oneElem) eq U32Val(42))
            certoraAssert(Vec.back(oneElem) eq U32Val(42))

            // Push another elem
            val twoElems = Vec.push_front(oneElem, U32Val(43))
            certoraAssert(Vec.len(twoElems) eq U32Val(2))
            certoraAssert(Vec.get(twoElems, U32Val(1)) eq U32Val(42))
            certoraAssert(Vec.get(twoElems, U32Val(0)) eq U32Val(43))
            certoraAssert(Vec.front(twoElems) eq U32Val(43))
            certoraAssert(Vec.back(twoElems) eq U32Val(42))

            // Check that oneElem was not affected
            certoraAssert(Vec.len(oneElem) eq U32Val(1))
            certoraAssert(Vec.get(oneElem, U32Val(0)) eq U32Val(42))
            certoraAssert(Vec.front(oneElem) eq U32Val(42))
            certoraAssert(Vec.back(oneElem) eq U32Val(42))
        })
    }

    @Test
    fun pop_back() {
        assertTrue(verifyWasm {
            val zeroElems = Vec.new()

            // Push a couple of elems
            val oneElem = Vec.push_back(zeroElems, U32Val(42))
            val twoElems = Vec.push_back(oneElem, U32Val(43))
            certoraAssert(Vec.len(twoElems) eq U32Val(2))
            certoraAssert(Vec.get(twoElems, U32Val(0)) eq U32Val(42))
            certoraAssert(Vec.get(twoElems, U32Val(1)) eq U32Val(43))

            // Pop an elem
            val popped = Vec.pop_back(twoElems)
            certoraAssert(Vec.len(popped) eq U32Val(1))
            certoraAssert(Vec.get(popped, U32Val(0)) eq U32Val(42))

            // Make sure the original object is unchanged
            certoraAssert(Vec.len(twoElems) eq U32Val(2))
            certoraAssert(Vec.get(twoElems, U32Val(0)) eq U32Val(42))
            certoraAssert(Vec.get(twoElems, U32Val(1)) eq U32Val(43))

            // Pop again
            val poppedTwice = Vec.pop_back(popped)
            certoraAssert(Vec.len(poppedTwice) eq U32Val(0))

            // Make sure the original object is unchanged
            certoraAssert(Vec.len(twoElems) eq U32Val(2))
            certoraAssert(Vec.get(twoElems, U32Val(0)) eq U32Val(42))
            certoraAssert(Vec.get(twoElems, U32Val(1)) eq U32Val(43))
        })
    }

    @Test
    fun pop_front() {
        assertTrue(verifyWasm {
            val zeroElems = Vec.new()

            // Push a couple of elems
            val oneElem = Vec.push_back(zeroElems, U32Val(42))
            val twoElems = Vec.push_back(oneElem, U32Val(43))
            certoraAssert(Vec.len(twoElems) eq U32Val(2))
            certoraAssert(Vec.get(twoElems, U32Val(0)) eq U32Val(42))
            certoraAssert(Vec.get(twoElems, U32Val(1)) eq U32Val(43))

            // Pop an elem
            val popped = Vec.pop_front(twoElems)
            certoraAssert(Vec.len(popped) eq U32Val(1))
            certoraAssert(Vec.get(popped, U32Val(0)) eq U32Val(43))

            // Make sure the original object is unchanged
            certoraAssert(Vec.len(twoElems) eq U32Val(2))
            certoraAssert(Vec.get(twoElems, U32Val(0)) eq U32Val(42))
            certoraAssert(Vec.get(twoElems, U32Val(1)) eq U32Val(43))

            // Pop again
            val poppedTwice = Vec.pop_front(popped)
            certoraAssert(Vec.len(poppedTwice) eq U32Val(0))

            // Make sure the original object is unchanged
            certoraAssert(Vec.len(twoElems) eq U32Val(2))
            certoraAssert(Vec.get(twoElems, U32Val(0)) eq U32Val(42))
            certoraAssert(Vec.get(twoElems, U32Val(1)) eq U32Val(43))
        })
    }

    @Test
    fun new_from_linear_memory() {
        assertTrue(verifyWasm {
            // Store some vals in memory
            for (i in 0..<4) {
                i64.store(i32((i * 8) + 1000), I32Val(i))
            }

            val map1 = Vec.new_from_linear_memory(U32Val(1000), U32Val(4))

            certoraAssert(Vec.len(map1) eq U32Val(4))
            for (i in 0..<4) {
                certoraAssert(Vec.get(map1, U32Val(i)) eq I32Val(i))
            }

            // Update elem 2 in memory, and check that it's not reflected in the buffer
            i32.store8(i32(1002), i32(111))
            certoraAssert(Vec.get(map1, U32Val(2)) eq I32Val(2))
        })
    }

    @Test
    fun unpack_to_linear_memory() {
        assertTrue(verifyWasm {
            // Store some vals in memory
            for (i in 0..<4) {
                i64.store(i32(i * 8), I32Val(i))
            }

            val map1 = Vec.new_from_linear_memory(U32Val(0), U32Val(4))

            // Write the first two elems to linear memory
            val res = Vec.unpack_to_linear_memory(map1, U32Val(66), U32Val(2))
            certoraAssert(res eq VoidVal)

            certoraAssert(i64.load(i32(66)) eq I32Val(0))
            certoraAssert(i64.load(i32(66 + 8)) eq I32Val(1))
        })
    }

    @Test
    fun insert() {
        assertTrue(verifyWasm {
            for (i in 0..<4) {
                i64.store(i32(i * 8), I32Val(i))
            }

            val map1 = Vec.new_from_linear_memory(U32Val(0), U32Val(4))

            // Insert an elem at position 2
            val map2 = Vec.insert(map1, U32Val(2), I32Val(42))

            certoraAssert(Vec.len(map2) eq U32Val(5))
            for ((i, v) in listOf(0L to 0, 1L to 1, 2L to 42, 3L to 2, 4L to 3)) {
                certoraAssert(Vec.get(map2, U32Val(i)) eq I32Val(v))
            }
        })
    }

    @Test
    fun delete() {
        assertTrue(verifyWasm {
            for (i in 0..<4) {
                i64.store(i32(i * 8), I32Val(i))
            }

            val map1 = Vec.new_from_linear_memory(U32Val(0), U32Val(4))

            // Delete the elem at position 2
            val map2 = Vec.del(map1, U32Val(2))

            certoraAssert(Vec.len(map2) eq U32Val(3))
            for ((i, v) in listOf(0L to 0, 1L to 1, 2L to 3)) {
                certoraAssert(Vec.get(map2, U32Val(i)) eq I32Val(v))
            }
        })
    }

    @Test
    fun slice() {
        assertTrue(verifyWasm {
            for (i in 0..<4) {
                i64.store(i32(i * 8), I32Val(i))
            }
            val map1 = Vec.new_from_linear_memory(U32Val(0), U32Val(4))

            // Take a slice of the middle 2 elems
            val map2 = Vec.slice(map1, U32Val(1), U32Val(3))

            certoraAssert(Vec.len(map2) eq U32Val(2))
            for ((i, v) in listOf(0L to 1, 1L to 2)) {
                certoraAssert(Vec.get(map2, U32Val(i)) eq I32Val(v))
            }
        })
    }
}
