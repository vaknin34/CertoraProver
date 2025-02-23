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
import wasm.host.soroban.Val.Tag.*
import wasm.wat.*

class BufModuleTest : SorobanTestFixture() {
    @Test
    fun new() {
        assertTrue(verifyWasm {
            val bytes = Buf.new()
            certoraAssert(Buf.len(bytes) eq U32Val(0))
        })
    }

    @Test
    fun push() {
        assertTrue(verifyWasm {
            val zeroBytes = Buf.new()

            // Push one byte and verifty that it worked
            val oneByte = Buf.push(zeroBytes, U32Val(42))
            certoraAssert(Buf.len(oneByte) eq U32Val(1))
            certoraAssert(Buf.get(oneByte, U32Val(0)) eq U32Val(42))

            // Push another byte
            val twoBytes = Buf.push(oneByte, U32Val(43))
            certoraAssert(Buf.len(twoBytes) eq U32Val(2))
            certoraAssert(Buf.get(twoBytes, U32Val(0)) eq U32Val(42))
            certoraAssert(Buf.get(twoBytes, U32Val(1)) eq U32Val(43))

            // Check that oneByte was not affected
            certoraAssert(Buf.len(oneByte) eq U32Val(1))
            certoraAssert(Buf.get(oneByte, U32Val(0)) eq U32Val(42))
        })
    }

    @Test
    fun pop() {
        assertTrue(verifyWasm {
            val zeroBytes = Buf.new()

            // Push a couple of bytes
            val oneByte = Buf.push(zeroBytes, U32Val(42))
            val twoBytes = Buf.push(oneByte, U32Val(43))
            certoraAssert(Buf.len(twoBytes) eq U32Val(2))
            certoraAssert(Buf.get(twoBytes, U32Val(0)) eq U32Val(42))
            certoraAssert(Buf.get(twoBytes, U32Val(1)) eq U32Val(43))

            // Pop a byte
            val popped = Buf.pop(twoBytes)
            certoraAssert(Buf.len(popped) eq U32Val(1))
            certoraAssert(Buf.get(popped, U32Val(0)) eq U32Val(42))

            // Make sure the original object is unchanged
            certoraAssert(Buf.len(twoBytes) eq U32Val(2))
            certoraAssert(Buf.get(twoBytes, U32Val(0)) eq U32Val(42))
            certoraAssert(Buf.get(twoBytes, U32Val(1)) eq U32Val(43))

            // Pop again
            val poppedTwice = Buf.pop(popped)
            certoraAssert(Buf.len(poppedTwice) eq U32Val(0))

            // Make sure the original object is unchanged
            certoraAssert(Buf.len(twoBytes) eq U32Val(2))
            certoraAssert(Buf.get(twoBytes, U32Val(0)) eq U32Val(42))
            certoraAssert(Buf.get(twoBytes, U32Val(1)) eq U32Val(43))
        })
    }

    @Test
    fun new_from_linear_memory() {
        assertTrue(verifyWasm {
            // Fill the first 4 bytes of memory
            for (i in 0..<4) {
                i32.store8(i32(i), i32(i))
            }

            val map1 = Buf.new_from_linear_memory(U32Val(0), U32Val(4))

            certoraAssert(Buf.len(map1) eq U32Val(4))
            for (i in 0..<4) {
                certoraAssert(Buf.get(map1, U32Val(i)) eq U32Val(i))
            }

            // Update byte 2 in memory, and check that it's not reflected in the buffer
            i32.store8(i32(2), i32(111))
            certoraAssert(Buf.get(map1, U32Val(2)) eq U32Val(2))
        })
    }

    @Test
    fun `new_from_linear_memory from static data`() {
        val theData = "1234"
        val dataLoc = 1000
        assertTrue(verifyWasm(
            watModule {
                memory()
                dataSegment("data", dataLoc, theData)
                global("data_start", i32, i32(dataLoc))
                global("data_end", i32, i32(dataLoc + theData.length))
                func(exportName = "entry").implement {
                    val buf = Buf.new_from_linear_memory(U32Val(dataLoc), U32Val(theData.length))

                    certoraAssert(Buf.len(buf) eq U32Val(theData.length))

                    for (i in 0..<theData.length) {
                        certoraAssert(Buf.get(buf, U32Val(i)) eq U32Val(theData[i].code))
                    }
                }
            },
            "entry"
        ))
    }

    @Test
    fun `new_from_linear_memory from uninitialized memory`() {
        assertTrue(verifyWasm {
            val buf1 = Buf.new_from_linear_memory(U32Val(0), U32Val(4))
            val buf2 = Buf.new_from_linear_memory(U32Val(0), U32Val(4))

            certoraAssert(Buf.len(buf1) eq U32Val(4))
            certoraAssert(Buf.len(buf2) eq U32Val(4))
            for (i in 0..<4) {
                certoraAssert(Buf.get(buf1, U32Val(i)) eq Buf.get(buf2, U32Val(i)))
            }
        })
    }


    @Test
    fun `new_from_linear_memory from dirty static data`() {
        val theData = "1234"
        val dataLoc = 1000
        assertFalse(verifyWasm(
            watModule {
                memory()
                dataSegment("data", dataLoc, theData)
                global("data_start", i32, i32(dataLoc))
                global("data_end", i32, i32(dataLoc + theData.length))
                func(exportName = "entry").implement {
                    i32.store8(i32(dataLoc), i32(42))

                    val buf = Buf.new_from_linear_memory(U32Val(dataLoc), U32Val(theData.length))

                    certoraAssert(Buf.len(buf) eq U32Val(theData.length))

                    for (i in 0..<theData.length) {
                        certoraAssert(Buf.get(buf, U32Val(i)) eq U32Val(theData[i].code))
                    }
                }
            },
            "entry"
        ))
    }

    @Test
    fun copy_to_linear_memory() {
        assertTrue(verifyWasm {
            for (i in 0..<4) {
                i32.store8(i32(i), i32(i))
            }
            val map1 = Buf.new_from_linear_memory(U32Val(0), U32Val(4))

            // Write the middle 2 bytes back to memory
            val res = Buf.copy_to_linear_memory(map1, U32Val(1), U32Val(66), U32Val(2))
            certoraAssert(res eq VoidVal)

            certoraAssert(i32.load8(i32(66)) eq i32(1))
            certoraAssert(i32.load8(i32(67)) eq i32(2))
        })
    }

    @Test
    fun insert() {
        assertTrue(verifyWasm {
            for (i in 0..<4) {
                i32.store8(i32(i), i32(i))
            }
            val map1 = Buf.new_from_linear_memory(U32Val(0), U32Val(4))

            // Insert a byte at position 2
            val map2 = Buf.insert(map1, U32Val(2), U32Val(42))

            certoraAssert(Buf.len(map2) eq U32Val(5))
            for ((i, v) in listOf(0L to 0L, 1L to 1L, 2L to 42L, 3L to 2L, 4L to 3L)) {
                certoraAssert(Buf.get(map2, U32Val(i)) eq U32Val(v))
            }
        })
    }

    @Test
    fun delete() {
        assertTrue(verifyWasm {
            for (i in 0..<4) {
                i32.store8(i32(i), i32(i))
            }
            val map1 = Buf.new_from_linear_memory(U32Val(0), U32Val(4))

            // Delete the byte at position 2
            val map2 = Buf.del(map1, U32Val(2))

            certoraAssert(Buf.len(map2) eq U32Val(3))
            for ((i, v) in listOf(0L to 0L, 1L to 1L, 2L to 3L)) {
                certoraAssert(Buf.get(map2, U32Val(i)) eq U32Val(v))
            }
        })
    }

    @Test
    fun `new_from_linear_memory equality`() {
        assertTrue(verifyWasm(
            watModule {
                memory("default", 65536)
                global("heap", i32, i32(10000))
                dataSegment("data", 1000, "abcd1234")

                func(exportName = "entry").implement {
                    val map1 = Buf.new_from_linear_memory(U32Val(1000), U32Val(4))
                    val map2 = Buf.new_from_linear_memory(U32Val(1000), U32Val(4))
                    val map3 = Buf.new_from_linear_memory(U32Val(1004), U32Val(4))
                    certoraAssert(map2 valEq map1)
                    certoraAssert(not(map3 valEq map1))
                }
            },
            "entry"
        ))
    }
}
