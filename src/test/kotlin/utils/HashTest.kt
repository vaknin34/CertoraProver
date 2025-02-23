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

package utils

import compiler.applyKeccak
import compiler.applyKeccakByHexStringConversion
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Assertions.assertEquals
import org.junit.jupiter.api.Test
import java.math.BigInteger

class HashTest {

    // thanks https://emn178.github.io/online-tools/keccak_256.html
    @Test
    fun testKeccak256() {
        val in1 = BigInteger.ZERO
        val res1 = "290decd9548b62a8d60345a988386fc84ba6bc95484008f6362f93160ef3e563".toBigInteger(16)
        Assertions.assertEquals(
            res1, applyKeccak(in1)
        )
        Assertions.assertEquals(
            res1, applyKeccakByHexStringConversion(in1)
        )

        val in2 = BigInteger.ONE
        val res2 = "b10e2d527612073b26eecdfd717e6a320cf44b4afac2b0732d9fcbe2b7fa0cf6".toBigInteger(16)
        Assertions.assertEquals(
            res2, applyKeccak(in2)
        )
        Assertions.assertEquals(
            res2, applyKeccakByHexStringConversion(in2)
        )

        val in3 = BigInteger.TWO
        val res3 = "405787fa12a823e0f2b7631cc41b3ba8828b3321ca811111fa75cd3aa3bb5ace".toBigInteger(16)
        Assertions.assertEquals(
            res3, applyKeccak(in3)
        )
        Assertions.assertEquals(
            res3, applyKeccakByHexStringConversion(in3)
        )

        val in4 = "0000000000000000000000ff0000000000000000000000000000000000000001".toBigInteger(16)
        val res4 = "10b889afe15e0cc960e833ac57c0d776ee4297da856c2ce5bb249c6cf8e195a4".toBigInteger(16)
        Assertions.assertEquals(
            res4, applyKeccak(in4)
        )
        Assertions.assertEquals(
            res4, applyKeccakByHexStringConversion(in4)
        )

        val in5 = "fe00000000000000000000ff0000000000000000000000000000000000000001".toBigInteger(16)
        val res5 = "600aa3c76636b2fec1e10e33f579753a2b9a434423d84ec9e49f21d05fd5ec96".toBigInteger(16)
        Assertions.assertEquals(
            res5, applyKeccak(in5)
        )
        Assertions.assertEquals(
            res5, applyKeccakByHexStringConversion(in5)
        )

    }
}