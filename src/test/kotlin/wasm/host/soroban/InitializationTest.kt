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
import wasm.wat.*

class InitializationTest : SorobanTestFixture() {
    private val testmodule = "\$testmodule"
    private val funcName = "\$fnm"

    @Test
    fun `locals initialized to zero`() {
        assertTrue(
            verifyWasm {
                certoraAssert(local(i32) eq i32(0))
                certoraAssert(local(u32) eq u32(0U))
                certoraAssert(local(i64) eq i64(0))
                certoraAssert(local(u64) eq u64(0U))
            }
        )
    }


    @Test
    fun `memory initialized to unconstrained`() {
        val memory =
            "(memory \$mem 65535)"
        val module = """
            (module $testmodule
                ${certoraAssert.import}
                $memory
                (func $funcName (export "entry")
                    i32.const 1234
                    i32.load
                    i32.eqz
                    call $certoraAssert))
        """.trimIndent()
        assertFalse(
            verifyWasm(module, entry = "entry")
        )
    }

    @Test
    fun `data segment unconstrained`() {
        val memory = "(memory \$mem 65535)"
        val data = "(data \$d (i32.const 1234) \"abcdefghi\")"
        val module = """
            (module $testmodule
                ${certoraAssert.import}
                $memory
                $data
                (func $funcName (export "entry")
                    i32.const 1234
                    i32.load
                    i32.eqz
                    call $certoraAssert))
        """.trimIndent()
        assertFalse(
            verifyWasm(module, entry = "entry")
        )
    }
}
