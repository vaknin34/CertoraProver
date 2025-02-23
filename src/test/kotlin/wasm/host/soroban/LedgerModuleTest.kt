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
import wasm.host.soroban.SorobanImport.Map
import wasm.host.soroban.SorobanImport.Ledger
import wasm.host.soroban.Val.Tag.*
import wasm.wat.*

class LedgerModuleTest : SorobanTestFixture() {
    companion object {
        val STORAGE_TYPE_TEMPORARY = i64(0)
        val STORAGE_TYPE_PERSISTENT = i64(1)
        val STORAGE_TYPE_INSTANCE = i64(2)
    }

    @Test
    fun `contract data with simple key`() {
        assertTrue(verifyWasm {
            for (i in 1..5) {
                Ledger.put_contract_data(U32Val(i), U32Val(i), STORAGE_TYPE_TEMPORARY)
            }
            for (i in 1..5) {
                certoraAssert(Ledger.has_contract_data(U32Val(i), STORAGE_TYPE_TEMPORARY) eq TrueVal)
                certoraAssert(Ledger.get_contract_data(U32Val(i), STORAGE_TYPE_TEMPORARY) eq U32Val(i))
            }
            for (i in 1..5) {
                Ledger.put_contract_data(U32Val(i), U32Val(i + 10), STORAGE_TYPE_PERSISTENT)
            }
            for (i in 1..5) {
                certoraAssert(Ledger.has_contract_data(U32Val(i), STORAGE_TYPE_TEMPORARY) eq TrueVal)
                certoraAssert(Ledger.get_contract_data(U32Val(i), STORAGE_TYPE_TEMPORARY) eq U32Val(i))
                certoraAssert(Ledger.has_contract_data(U32Val(i), STORAGE_TYPE_PERSISTENT) eq TrueVal)
                certoraAssert(Ledger.get_contract_data(U32Val(i), STORAGE_TYPE_PERSISTENT) eq U32Val(i + 10))
            }
            Ledger.del_contract_data(U32Val(3), STORAGE_TYPE_TEMPORARY)
            certoraAssert(Ledger.has_contract_data(U32Val(3), STORAGE_TYPE_TEMPORARY) eq FalseVal)
            certoraAssert(Ledger.has_contract_data(U32Val(3), STORAGE_TYPE_PERSISTENT) eq TrueVal)
        })
    }

    @Test
    fun `contract data with string key`() {
        assertTrue(verifyWasm(
            watModule {
                memory()
                dataSegment("d0", 1000, "key1")
                dataSegment("d1", 2000, "key2")
                func(exportName = "entry").implement {
                    val key1 = Buf.string_new_from_linear_memory(U32Val(1000), U32Val(4))
                    val key2 = Buf.string_new_from_linear_memory(U32Val(2000), U32Val(4))
                    val key2Copy = Buf.string_new_from_linear_memory(U32Val(2000), U32Val(4))

                    certoraAssert(key2Copy valEq key2)

                    Ledger.put_contract_data(key1, U32Val(1), STORAGE_TYPE_TEMPORARY)
                    Ledger.put_contract_data(key2, U32Val(2), STORAGE_TYPE_PERSISTENT)

                    certoraAssert(Ledger.has_contract_data(key1, STORAGE_TYPE_TEMPORARY) eq TrueVal)
                    certoraAssert(Ledger.get_contract_data(key1, STORAGE_TYPE_TEMPORARY) eq U32Val(1))
                    certoraAssert(Ledger.has_contract_data(key2, STORAGE_TYPE_PERSISTENT) eq TrueVal)
                    certoraAssert(Ledger.get_contract_data(key2, STORAGE_TYPE_PERSISTENT) eq U32Val(2))
                    certoraAssert(Ledger.has_contract_data(key2Copy, STORAGE_TYPE_PERSISTENT) eq TrueVal)
                    certoraAssert(Ledger.get_contract_data(key2Copy, STORAGE_TYPE_PERSISTENT) eq U32Val(2))
                }
            },
            "entry"
        ))
    }

    @Test
    fun `nondet contract data - two equal keys produce equal values`() {
        assertTrue(verifyWasm(
            watModule {
                memory()
                dataSegment("d0", 1000, "key1")
                func(exportName = "entry").implement {
                    val key1 = Buf.string_new_from_linear_memory(U32Val(1000), U32Val(4))
                    val key2 = Buf.string_new_from_linear_memory(U32Val(1000), U32Val(4))

                    val map1 = Ledger.get_contract_data(key1, STORAGE_TYPE_TEMPORARY)
                    val map2 = Ledger.get_contract_data(key2, STORAGE_TYPE_TEMPORARY)

                    certoraAssert(map1 valEq map2)

                    certoraAssert(Map.get(map1, U32Val(1)) eq Map.get(map2, U32Val(1)))
                }
            },
            "entry",
            assumeNoTraps = true
        ))
    }
}
