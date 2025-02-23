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

package evm

import utils.*
import java.math.BigInteger

fun highOnes(width: Int) = MAX_EVM_UINT256 - lowOnes(EVM_BITWIDTH256 - width)
/** bits are 1 from bit 0 up to bit [end] (non-inclusive) */
fun lowOnes(end: Int) = BigInteger.ONE.shiftLeft(end) - BigInteger.ONE
/** bits are 1 from bit [start] up to bit [end] (non-inclusive) */
fun onesRange(start: Int, end: Int) = lowOnes(end) - lowOnes(start)

fun signedIntsWithSameSign(a: BigInteger, b: BigInteger): Boolean =
    a > MAX_EVM_INT256 && b > MAX_EVM_INT256 ||
    a <= MAX_EVM_INT256 && b <= MAX_EVM_INT256

fun BigInteger.to2s() =
    when {
        this in BigInteger.ZERO.. MAX_EVM_INT256 -> this
        this in MIN_EVM_INT256_AS_MATH_INT..<BigInteger.ZERO -> this + EVM_MOD_GROUP256
        else -> error("$this is not within the range that can be translated to 2s complement.")
    }

fun Int.to2s() = toBigInteger().to2s()
fun Long.to2s() = toBigInteger().to2s()

fun BigInteger.from2s() =
    when (this) {
        in BigInteger.ZERO..MAX_EVM_INT256 -> this
        in MIN_EVM_INT256_2S_COMPLEMENT..MAX_EVM_UINT256 -> this - EVM_MOD_GROUP256
        else -> error("$this is not within the range that can be translated from 2s complement.")
    }

fun Int.from2s() = toBigInteger().from2s()
fun Long.from2s() = toBigInteger().from2s()

object EVMOps {
    fun add(a: BigInteger, b: BigInteger) = (a + b).mod(EVM_MOD_GROUP256)
    fun sub(a: BigInteger, b: BigInteger) = (a - b).mod(EVM_MOD_GROUP256)
    fun mul(a: BigInteger, b: BigInteger) = (a * b).mod(EVM_MOD_GROUP256)
    fun div(a: BigInteger, b: BigInteger) = when {
        // https://github.com/ethereum/go-ethereum/blob/da29332c5f4c368ff03ec4e7132eefac48fed1ae/core/vm/instructions.go#L65
        // yes, returning zero makes zero sense.
        b == BigInteger.ZERO -> BigInteger.ZERO
        else -> a / b
    }
    // https://github.com/ethereum/go-ethereum/blob/da29332c5f4c368ff03ec4e7132eefac48fed1ae/core/vm/instructions.go#L76
    fun sdiv(a: BigInteger, b: BigInteger) = when {
        b == BigInteger.ZERO -> BigInteger.ZERO
        // `minInt256 / -1 = minInt256`. This is actually an overflow, but EVM defines it this way.
        a == MIN_EVM_INT256_2S_COMPLEMENT && b == MAX_EVM_UINT256 -> MIN_EVM_INT256_2S_COMPLEMENT
        else -> (a.from2s() / b.from2s()).to2s()
    }

    fun exp(a: BigInteger, b: BigInteger) = a.modPow(b, EVM_MOD_GROUP256)

    // https://github.com/ethereum/go-ethereum/blob/da29332c5f4c368ff03ec4e7132eefac48fed1ae/core/vm/instructions.go#L95
    fun mod(a: BigInteger, m: BigInteger) = when (m) {
        BigInteger.ZERO -> BigInteger.ZERO
        else -> a.mod(m).mod(EVM_MOD_GROUP256)
    }


    /**
     * EVM mod cares only for the sign in the nominator. So:
     *      12 %  5 =  2
     *      12 % -5 =  2
     *     -12 %  5 = -2
     *     -12 % -5 = -2
     * Of course in EVM these are represented in 2s complement.
     *
     * https://github.com/ethereum/go-ethereum/blob/da29332c5f4c368ff03ec4e7132eefac48fed1ae/core/vm/instructions.go#L106
     */
    fun smod(a: BigInteger, m: BigInteger) : BigInteger = when (m) {
        BigInteger.ZERO -> BigInteger.ZERO
        else -> {
            val aa = a.from2s()
            val mm = m.from2s().abs()
            aa.abs().mod(mm).letIf(aa < BigInteger.ZERO) { -it }.to2s()
        }
    }

    /**
    * Sign extends [b] from ([a] + 1) * 8 bits to 256 bits.
    * The implementation operates on the low-level, bit representation of [b] and treats [b] as if
    * it is an intK (in particular, it does not rely on its encoding as a [BigInteger] and
    * ignores the actual [BigInteger] sign bit of [b]).
    *
    * @param[a] The index of the most significant byte of [b]. At least 0 and at most 31.
    *
    * @param[b] Signed (two's complement) integer where (([a] + 1) * 8)-1 is assumed to be
    * the index of its sign bit. That is, the type of [b] is seen as Solidity's intK where K is given by [a].
    *
    * @return [b] encoded as if its type is Solidity's int256.
    */
    fun signExtend(a: BigInteger, b: BigInteger): BigInteger {
        check(a >= BigInteger.ZERO && a < EVM_WORD_SIZE) {
            "Expected a to be a byte offset at least 0 and less than $EVM_WORD_SIZE, but got a=$a"
        }
        val bitLengthOfB = (a + BigInteger.ONE) * 8.toBigInteger()
        val bSignBitPos = bitLengthOfB - BigInteger.ONE
        val bSignBitValue: Boolean =
            b.and(BigInteger.ZERO.setBit(bSignBitPos.intValueExact())) != BigInteger.ZERO
        val bOnesMask =
            BigInteger.ZERO.setBit(bitLengthOfB.intValueExact()) - BigInteger.ONE /* 2^[bitLengthOfB]-1 */

        return if (!bSignBitValue) { /* b is non-negative; extend with leading zeroes */
            b.and(bOnesMask.or(EVM_MOD_GROUP256))
        } else { /* b is negative; extend with leading ones */
            check(bSignBitValue)
            b.or(MAX_EVM_UINT256 - bOnesMask)
        }
    }

    fun addMod(a: BigInteger, b: BigInteger, m: BigInteger) = a.add(b).mod(m)
    fun mulMod(a: BigInteger, b: BigInteger, m: BigInteger) = a.multiply(b).mod(m)

    fun isZero(a: BigInteger) = if (a == BigInteger.ZERO) BigInteger.ONE else BigInteger.ZERO

    fun not(a: BigInteger) = MAX_EVM_UINT256.andNot(a)
    fun and(a: BigInteger, b: BigInteger) = a and b
    fun or(a: BigInteger, b: BigInteger) = a or b
    fun xor(a: BigInteger, b: BigInteger) = a xor b

    fun shl(a: BigInteger, b: BigInteger) = when {
        b >= EVM_BITWIDTH256_BIGINT -> BigInteger.ZERO
        else -> a.shiftLeft(b.intValueExact()).mod(EVM_MOD_GROUP256)
    }

    fun shr(a: BigInteger, b: BigInteger) = when {
        b >= EVM_BITWIDTH256_BIGINT -> BigInteger.ZERO
        else -> a / BigInteger.TWO.pow(b.intValueExact()) // doesn't do sign-extension
    }

    fun sar(a: BigInteger, b: BigInteger) = when {
        b >= EVM_BITWIDTH256_BIGINT ->
            if (a <= MAX_EVM_INT256) { BigInteger.ZERO } else { MAX_EVM_UINT256 }
        else -> {
            val k = b.intValueExact()
            if (a <= MAX_EVM_INT256) {
                a shr k
            } else {
                (a shr k) + highOnes(k)
            }
        }
    }

    fun eq(a: BigInteger, b: BigInteger) = if (a == b) BigInteger.ONE else BigInteger.ZERO

    fun lt(a: BigInteger, b: BigInteger) = if (a < b) BigInteger.ONE else BigInteger.ZERO
    fun gt(a: BigInteger, b: BigInteger) = lt(b, a)
    fun le(a: BigInteger, b: BigInteger) = if (a == b) BigInteger.ONE else lt(a, b)
    fun ge(a: BigInteger, b: BigInteger) = le(b, a)

    fun slt(a: BigInteger, b: BigInteger) = when {
        // if both have the same sign, return a < b
        signedIntsWithSameSign(a, b) -> if (a < b) BigInteger.ONE else BigInteger.ZERO
        // if a is negative but b is positive
        a > MAX_EVM_INT256 && b <= MAX_EVM_INT256 -> BigInteger.ONE
        else -> BigInteger.ZERO
    }
    fun sgt(a: BigInteger, b: BigInteger) = slt(b, a)

    fun sle(a: BigInteger, b: BigInteger) = if (a == b) BigInteger.ONE else slt(a, b)
    fun sge(a: BigInteger, b: BigInteger) = sle(b, a)
}
