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
import wasm.host.soroban.SorobanImport.Address
import wasm.host.soroban.SorobanImport.CVT
import wasm.host.soroban.Val.Tag.*
import wasm.wat.*

class AddressModuleTest : SorobanTestFixture() {
    @Test
    fun `require_auth failure`() {
        assertTrue(verifyWasm(
            watFunc("entry", i64) { addr ->
                certoraAssume(CVT.is_auth(addr) eq FalseVal)
                Address.require_auth(addr)
                certoraAssert(i32(0))
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `require_auth success`() {
        assertFalse(verifyWasm(
            watFunc("entry", i64) { addr ->
                certoraAssume(CVT.is_auth(addr) eq TrueVal)
                Address.require_auth(addr)
                certoraAssert(i32(0))
            },
            "entry",
            assumeNoTraps = true
        ))
    }

    @Test
    fun `address_to_strkey returns consistent strings`() {
        assertTrue(verifyWasm(
            watFunc("entry", i64) { addr ->
                val str1 = Address.address_to_strkey(addr)
                val str2 = Address.address_to_strkey(addr)
                certoraAssert(str1 eq str2)
            },
            "entry",
            assumeNoTraps = true
        ))
    }
}
