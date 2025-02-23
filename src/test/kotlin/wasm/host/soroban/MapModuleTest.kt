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

import config.Config
import config.ConfigScope
import org.junit.jupiter.api.*
import org.junit.jupiter.api.Assertions.*
import wasm.*
import wasm.host.soroban.SorobanImport.Buf
import wasm.host.soroban.SorobanImport.Map
import wasm.host.soroban.SorobanImport.Vec
import wasm.host.soroban.Val.Tag.*
import wasm.wat.*

class MapModuleTest : SorobanTestFixture() {

    val disableGrounding = ConfigScope(Config.Smt.GroundQuantifiers, false)

    @Test
    fun new() {
        assertTrue(verifyWasm {
            val map = Map.new()
            certoraAssert(Map.len(map) eq U32Val(0))
        })
    }

    @Test
    fun put() {
        assertTrue(verifyWasm {
            val map = Map.new()
            certoraAssert(Map.len(map) eq U32Val(0))
            certoraAssert(Map.has(map, U32Val(42)) eq FalseVal)

            val map1 = Map.put(map, U32Val(42), U32Val(43))
            certoraAssert(Map.len(map1) eq U32Val(1))
            certoraAssert(Map.has(map1, U32Val(42)) eq TrueVal)
            certoraAssert(Map.has(map1, U32Val(43)) eq FalseVal)
            certoraAssert(Map.get(map1, U32Val(42)) eq U32Val(43))

            val map2 = Map.put(map1, U32Val(44), U32Val(45))
            certoraAssert(Map.len(map2) eq U32Val(2))
            certoraAssert(Map.has(map2, U32Val(42)) eq TrueVal)
            certoraAssert(Map.has(map2, U32Val(43)) eq FalseVal)
            certoraAssert(Map.has(map2, U32Val(44)) eq TrueVal)
            certoraAssert(Map.get(map2, U32Val(44)) eq U32Val(45))

            // Overwrite an existing key
            val map3 = Map.put(map2, U32Val(42), U32Val(42))
            certoraAssert(Map.len(map3) eq U32Val(2))
            certoraAssert(Map.has(map3, U32Val(42)) eq TrueVal)
            certoraAssert(Map.has(map3, U32Val(43)) eq FalseVal)
            certoraAssert(Map.has(map3, U32Val(44)) eq TrueVal)
            certoraAssert(Map.get(map3, U32Val(42)) eq U32Val(42))
        })
    }

    @Test
    fun del() {
        assertTrue(verifyWasm {
            val map = Map.new()
            val map1 = Map.put(map, U32Val(42), U32Val(43))
            val map2 = Map.put(map1, U32Val(44), U32Val(45))
            val map3 = Map.put(map2, U32Val(46), U32Val(47))

            val map3Del = Map.del(map3, U32Val(44))
            certoraAssert(Map.len(map3Del) eq U32Val(2))
            certoraAssert(Map.has(map3Del, U32Val(42)) eq TrueVal)
            certoraAssert(Map.has(map3Del, U32Val(44)) eq FalseVal)
            certoraAssert(Map.has(map3Del, U32Val(46)) eq TrueVal)
            certoraAssert(Map.get(map3Del, U32Val(42)) eq U32Val(43))
            certoraAssert(Map.get(map3Del, U32Val(46)) eq U32Val(47))

            val map1Del = Map.del(map1, U32Val(42))
            certoraAssert(Map.len(map1Del) eq U32Val(0))
            certoraAssert(Map.has(map1Del, U32Val(42)) eq FalseVal)
            certoraAssert(Map.has(map1Del, U32Val(44)) eq FalseVal)
        })
    }

    @Test
    fun key_by_pos() {
        assertTrue(verifyWasm {
            val map = (1..5).fold(Map.new()) { acc, m -> Map.put(acc, U32Val(m), U32Val(m + 5)) }

            // We don't guarantee any particular key ordering.  But we can still verify some things.

            // Check that the key at each index is a valid key
            fun isValidKey(i: Int) = (1..5).fold(i32(0)) { acc, j ->
                acc or (Map.key_by_pos(map, U32Val(i)) eq U32Val(j))
            }
            for (i in 0..<5) {
                certoraAssert(isValidKey(i))
            }

            // Check that each key is unique
            fun isUniqueKey(i: Int) = (0..<5).toSet().minus(i).fold(i32(1)) { acc, j ->
                acc and (Map.key_by_pos(map, U32Val(i)) ne Map.key_by_pos(map, U32Val(j)))
            }
            for (i in 0..<5) {
                certoraAssert(isUniqueKey(i))
            }
        })
    }

    @Test
    fun val_by_pos() {
        assertTrue(verifyWasm {
            val map = (1..5).fold(Map.new()) { acc, m -> Map.put(acc, U32Val(m), U32Val(m + 5)) }

            // Check that the value at each index is the value corresponding to the key at that index
            for (i in 0..<5) {
                certoraAssert(
                    Map.val_by_pos(map, U32Val(i)) eq Map.get(map, Map.key_by_pos(map, U32Val(i)))
                )
            }
        })
    }

    @Test
    fun keys() {
        // TODO CERT-6734: the map_keys and map_values functions currently don't work with grounding enabled
        disableGrounding.use {
            assertTrue(verifyWasm {
                val map = (1..5).fold(Map.new()) { acc, m -> Map.put(acc, U32Val(m), U32Val(m + 5)) }
                val keys = Map.keys(map)

                // Check that the key at each index is a valid key
                fun isValidKey(i: Int) = (1..5).fold(i32(0)) { acc, j ->
                    acc or (Vec.get(keys, U32Val(i)) eq U32Val(j))
                }
                for (i in 0..<5) {
                    certoraAssert(isValidKey(i))
                }

                // Check that each key is unique
                fun isUniqueKey(i: Int) = (0..<5).toSet().minus(i).fold(i32(1)) { acc, j ->
                    acc and (Vec.get(keys, U32Val(i)) ne Vec.get(keys, U32Val(j)))
                }
                for (i in 0..<5) {
                    certoraAssert(isUniqueKey(i))
                }
            })
        }
    }

    @Test
    fun values() {
        // TODO CERT-6734: the map_keys and map_values functions currently don't work with grounding enabled
        disableGrounding.use {
            assertTrue(verifyWasm {
                val map = (1..5).fold(Map.new()) { acc, m -> Map.put(acc, U32Val(m), U32Val(m + 5)) }
                val keys = Map.keys(map)
                val vals = Map.values(map)

                // Check that the value at each index is the value corresponding to the key at that index
                for (i in 0..<5) {
                    certoraAssert(
                        Vec.get(vals, U32Val(i)) eq Map.get(map, Vec.get(keys, U32Val(i)))
                    )
                }
            })
        }
    }

    @Test
    fun unpack_pack_unpack_map() {
        val dataStart: Int = 0x0100
        val four = byteArrayOf(0x04, 0, 0, 0)
        val keysStrings = byteArrayOf(0x00, 0x01, 0x00, 0x00)
        val keysStringsPlusFour = byteArrayOf(0x04, 0x01, 0x00, 0x00)
        val keysSlice = 0x0108

        val data = "key1key2".toByteArray() + keysStrings + four + keysStringsPlusFour + four

        val module = watModule {
            memory("default_memory", 65536)
            dataSegment("ro.data", dataStart, data)
            func(WatLocal(i64, "p0"), exportName = "entry").implement {(m) ->
                val preValues = local(i64, "l0")
                val key1Value = local(i64, "l1")
                val key2Value = local(i64, "l2")
                val postValues = local(i64, "l3")
                val m2 = local(i64, "m2")

                for (i in 0..31) {
                    i64.store(i32(i*8), i64(123L + i))
                }

                // These addresses should not change
                preValues.set(i64.load(i32(0)))
                postValues.set(i64.load(i32(0x20)))

                // Unpack the values to memory
                // writes values to 0x10 and 0x18
                Map.unpack_to_linear_memory(m, U32Val(keysSlice), U32Val(0x10), U32Val(2))

                // boundaries unchanged
                certoraAssert( i64.load(i32(0x00)) eq preValues)
                certoraAssert( i64.load(i32(0x20)) eq postValues)

                // Swap values
                i64.load(i32(0x10))
                key1Value.set(i64.load(i32(0)))
                i64.load(i32(0x18))
                key2Value.set(i64.load(i32(0)))
                i64.store(i32(0x10), key2Value)
                i64.store(i32(0x18), key1Value)

                m2.set(Map.new_from_linear_memory(U32Val(keysSlice), U32Val(0x10), U32Val(2)))
                Map.unpack_to_linear_memory(m2, U32Val(keysSlice), U32Val(0x10), U32Val(2))

                // boundaries unchanged
                certoraAssert( i64.load(i32(0x00)) eq preValues)
                certoraAssert( i64.load(i32(0x20)) eq postValues)
                // keys swapped
                certoraAssert(i64.load(i32(0x10)) eq key2Value)
                certoraAssert(i64.load(i32(0x18)) eq key1Value)
            }
        }
        assertTrue(verifyWasm(module, "entry", assumeNoTraps = true))
    }

    @Test
    fun `nondet map is not necessarily empty`() {
        assertFalse(verifyWasm(
            watFunc("entry", i64) { map ->
                certoraAssert((Map.len(map) ne U32Val(0)).eqz())
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `nondet map might be empty`() {
        assertFalse(verifyWasm(
            watFunc("entry", i64) { map ->
                certoraAssert((Map.len(map) eq U32Val(0)).eqz())
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `nondet map might contain key 0`() {
        assertFalse(verifyWasm(
            watFunc("entry", i64) { map ->
                certoraAssert((Map.has(map, U32Val(0)) eq TrueVal).eqz())
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `nondet map might not contain key 0`() {
        assertFalse(verifyWasm(
            watFunc("entry", i64) { map ->
                certoraAssert((Map.has(map, U32Val(0)) eq FalseVal).eqz())
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `nondet map might have any value 42 at key 1234`() {
        assertFalse(verifyWasm(
            watFunc("entry", i64) { map ->
                certoraAssert((Map.get(map, U32Val(1234)) eq U32Val(42)).eqz())
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `nondet map might have value 43 at key 1234`() {
        assertFalse(verifyWasm(
            watFunc("entry", i64) { map ->
                certoraAssert((Map.get(map, U32Val(1234)) eq U32Val(43)).eqz())
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `nondet map plus known entry definitely contains the known value`() {
        assertTrue(verifyWasm(
            watFunc("entry", i64) { map ->
                val map1 = Map.put(map, U32Val(1234), U32Val(42))
                certoraAssert(Map.get(map1, U32Val(1234)) eq U32Val(42))
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `nondet map plus known entry has size greater than 0`() {
        assertTrue(verifyWasm(
            watFunc("entry", i64) { map ->
                val map1 = Map.put(map, U32Val(1234), U32Val(42))
                certoraAssert(Map.len(map1).decodeU32Val() gt u32(0u))
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `nondet map plus known entry might have another entry`() {
        assertFalse(verifyWasm(
            watFunc("entry", i64) { map ->
                val map1 = Map.put(map, U32Val(1234), U32Val(42))
                certoraAssert((Map.get(map1, U32Val(1235)) eq U32Val(43)).eqz())
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `nondet map not affected by allocated map`() {
        assertTrue(verifyWasm(
            watFunc("entry", i64) { map ->
                val before = Map.get(map, U32Val(1))
                Map.put(map, U32Val(1), U32Val(2))
                val after = Map.get(map, U32Val(1))
                certoraAssert(before eq after)
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `keys have structural equality semantics`() {
        val wat = watModule {
            memory()
            dataSegment("d0", 1000, "key1")
            dataSegment("d1", 2000, "key2")
            func(exportName = "entry").implement {
                val key1 = Buf.string_new_from_linear_memory(U32Val(1000), U32Val(4))
                val key2 = Buf.string_new_from_linear_memory(U32Val(2000), U32Val(4))
                val key2Copy = Buf.string_new_from_linear_memory(U32Val(2000), U32Val(4))

                certoraAssume(not(key1 valEq key2)) // Need this since we don't write the actual data segment data yet
                certoraAssert(key2Copy valEq key2)

                var map = Map.new()
                map = Map.put(map, key1, U32Val(42))
                map = Map.put(map, key2, U32Val(43))

                certoraAssert(Map.get(map, key1) eq U32Val(42))
                certoraAssert(Map.get(map, key2) eq U32Val(43))
                certoraAssert(Map.get(map, key2Copy) eq U32Val(43))

                map = Map.put(map, key2Copy, U32Val(44))
                certoraAssert(Map.get(map, key2) eq U32Val(44))
                certoraAssert(Map.get(map, key2Copy) eq U32Val(44))
            }
        }
        assertTrue(verifyWasm(
            wat,
            "entry",
            assumeNoTraps = false
        ))
    }
}
