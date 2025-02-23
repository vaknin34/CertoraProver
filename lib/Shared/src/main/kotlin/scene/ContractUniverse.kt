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

package scene

import evm.ECRECOVER_PRECOMPILED_ADDRESS
import evm.SHA256_PRECOMPILED_ADDRESS
import evm.IDENTITY_PRECOMPILED_ADDRESS
import java.math.BigInteger

/* describes precompiled contracts of a particular 'universe', i.e. Ethereum (and its forks), or Celo */
enum class ContractUniverse {
    ETHEREUM,
    CELO
    ;
    // ETHEREUM has 9 precompiled contracts. CELO has 256
    // # of precompiled in ethereum: istanbul - 9, byzantium - 8, homestead - 4. Always from 1 to N

    val addresses
        get() = when (this) {
            ETHEREUM -> (1 until 9) /* ISTANBUL */ + (244 until 255) /* CELO */
            CELO -> 1 until 255
        }.map { it.toBigInteger() }

    fun getNameOfPrecompiledByAddress(i: BigInteger) = when (i) {
        ECRECOVER_PRECOMPILED_ADDRESS -> "ecrecover" // recovery of ecdsa signature
        SHA256_PRECOMPILED_ADDRESS -> "sha256" // a hash function
        3.toBigInteger() -> "ripemd160" // a hash function
        IDENTITY_PRECOMPILED_ADDRESS -> "identity" // data copy
        5.toBigInteger() -> "bigmod" // modular exponentiation
        6.toBigInteger() -> "bn256Add" // elliptic curve
        7.toBigInteger() -> "bn256ScalarMul" // elliptic curve
        8.toBigInteger() -> "bn256Pairing" // elliptic curve
        9.toBigInteger() -> "blake2b" // a hash function
        else -> null
    }

    fun isPrecompiled(i: BigInteger) = when (this) {
        ETHEREUM -> BigInteger.ONE <= i && i <= BigInteger.valueOf(
            9
        )
        CELO -> BigInteger.ONE <= i && i <= BigInteger.valueOf(
            256
        )
    }
}
