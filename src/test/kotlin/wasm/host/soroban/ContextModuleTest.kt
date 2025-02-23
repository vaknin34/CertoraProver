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
import wasm.host.soroban.SorobanImport.Context
import wasm.host.soroban.SorobanImport.Vec
import wasm.host.soroban.Val.Tag.*
import wasm.wat.*

class ContextModuleTest : SorobanTestFixture() {
    @Test
    fun log_from_linear_memory() {
        assertTrue(verifyWasm {
            Context.log_from_linear_memory(U32Val(0), U32Val(0), U32Val(0), U32Val(0))
        })
    }

    @Test
    fun contract_event() {
        assertTrue(verifyWasm {
            Context.contract_event(Vec.new(), U32Val(0))
        })
    }

    @Test
    fun get_ledger_version() {
        assertTrue(verifyWasm {
            val v1 = Context.get_ledger_version()
            val v2 = Context.get_ledger_version()
            certoraAssert(v1 eq v2)
        })
    }

    @Test
    fun get_ledger_sequence() {
        assertTrue(verifyWasm {
            val v1 = Context.get_ledger_sequence()
            val v2 = Context.get_ledger_sequence()
            certoraAssert(v1 eq v2)
        })
    }

    @Test
    fun get_ledger_timestamp() {
        assertTrue(verifyWasm {
            val v1 = Context.get_ledger_timestamp()
            val v2 = Context.get_ledger_timestamp()
            certoraAssert(v1 valEq v2)
        })
    }

    @Test
    fun fail_with_error() {
        assertTrue(verifyWasm(assumeNoTraps = true) {
            Context.fail_with_error(Error(0))
            certoraAssert(i32(1))
        })
        assertFalse(verifyWasm(assumeNoTraps = false) {
            Context.fail_with_error(Error(0))
            certoraAssert(i32(1))
        })
    }

    @Test
    fun get_ledger_network_id() {
        assertTrue(verifyWasm {
            val v1 = Context.get_ledger_network_id()
            val v2 = Context.get_ledger_network_id()
            certoraAssert(v1 eq v2)
        })
    }

    @Test
    fun get_current_contract_address() {
        assertTrue(verifyWasm {
            val v1 = Context.get_current_contract_address()
            val v2 = Context.get_current_contract_address()
            certoraAssert(v1 eq v2)
            certoraAssert(v1 valEq v2)
        })
    }

    @Test
    fun get_max_live_until_ledger() {
        assertTrue(verifyWasm {
            val v1 = Context.get_max_live_until_ledger()
            val v2 = Context.get_max_live_until_ledger()
            certoraAssert(v1 eq v2)
        })
    }

    @Test
    fun `2 and 2 are equal`() {
        assertTrue(verifyWasm {
            certoraAssert(Context.obj_cmp(U32Val(2), U32Val(2)) eq i64(0))
        })
    }

    @Test
    fun `2 and 3 are not equal`() {
        assertTrue(verifyWasm {
            certoraAssert(Context.obj_cmp(U32Val(2), U32Val(3)) ne i64(0))
        })
    }

    @Test
    fun `2 might be less than 3`() {
        assertFalse(verifyWasm {
            certoraAssert(Context.obj_cmp(U32Val(2), U32Val(3)) eq i64(1))
        })
    }

    // Note that we just don't implement < and > yet, so it's nondet, even in simple cases.
    @Test
    fun `2 might be greater than 3`() {
        assertFalse(verifyWasm {
            certoraAssert(Context.obj_cmp(U32Val(2), U32Val(3)) eq i64(-1))
        })
    }
}
