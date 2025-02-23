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

package analysis.icfg

import analysis.numeric.IntValue
import evm.MAX_EVM_UINT256
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.math.BigInteger

class IntervalToByteRangeTest {
    private fun BigInteger.bytesLength() = (this.bitLength() + 7) and 7.inv()

    private fun shiftToTop(v: BigInteger, padBytes: Int = 0) : BigInteger {
        val roundedUp = v.bytesLength() + padBytes * 8
        val shiftAmount = 256 - roundedUp
        check(shiftAmount >= 0)
        return v.shiftLeft(shiftAmount)
    }

    private fun shiftToTop(v: Int, padBytes: Int = 0) : BigInteger {
        return shiftToTop(v.toBigInteger(), padBytes)
    }

    private fun toConstantPrefix(constantPrefix: Int, lowerPart: Int, upperPart: Int, padBytes: Int = 0) : IntValue {
        return toConstantPrefix(constantPrefix.toBigInteger(), lowerPart.toBigInteger(), upperPart.toBigInteger(), padBytes)
    }

    private fun toConstantPrefix(constantPrefix: BigInteger, lowerPart: BigInteger, upperPart: BigInteger, padBytes: Int = 0) : IntValue {
        require(lowerPart <= upperPart)
        val shiftAmount = upperPart.bytesLength()
        val constantSizeInByteAlignedBits = constantPrefix.bytesLength()
        require(constantSizeInByteAlignedBits + shiftAmount + padBytes * 8 <= 256)
        val padAmount = padBytes * 8
        Assertions.assertEquals(constantPrefix.shiftLeft(shiftAmount + padAmount) or upperPart.shiftLeft(padAmount),
            constantPrefix.shiftLeft(shiftAmount + padAmount) + upperPart.shiftLeft(padAmount))
        Assertions.assertEquals(constantPrefix.shiftLeft(shiftAmount + padAmount) or lowerPart.shiftLeft(padAmount),
            constantPrefix.shiftLeft(shiftAmount + padAmount) + lowerPart.shiftLeft(padAmount))
        return IntValue(
            lb = constantPrefix.shiftLeft(shiftAmount + padAmount) + lowerPart.shiftLeft(padAmount),
            ub = constantPrefix.shiftLeft(shiftAmount + padAmount) + upperPart.shiftLeft(padAmount)
        )
    }

    @Test
    fun testShifting() {
        Assertions.assertEquals(BigInteger("b00000000000000000000000000000000000000000000000000000000000000", 16), shiftToTop(0xb.toBigInteger()))
        Assertions.assertEquals(BigInteger("bb00000000000000000000000000000000000000000000000000000000000000", 16), shiftToTop(BigInteger("bb00", 16)))
        Assertions.assertEquals(MAX_EVM_UINT256, shiftToTop(MAX_EVM_UINT256))
        Assertions.assertEquals(MAX_EVM_UINT256 - BigInteger.ONE, shiftToTop(MAX_EVM_UINT256 - BigInteger.ONE))
    }

    private fun Int.lift() = IntValue.Constant(this.toBigInteger())
    private fun BigInteger.lift() = IntValue.Constant(this)

    private val nullNext : () -> IntValue? = { -> null }

    operator fun ScratchByteRange.Companion.invoke(start: Int, end: Int) : ScratchByteRange = ScratchByteRange(
        from = start.toBigInteger(),
        to = end.toBigInteger()
    )

    @Test
    fun extractConstantPrefix() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            0, 3, 0.lift(), nullNext
        )
        Assertions.assertEquals(ScratchByteRange(0, 2) to BigInteger.ZERO, res)
    }

    @Test
    fun ignoreLowerBits() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            0, 3, 28.lift(), nullNext
        )
        Assertions.assertEquals(ScratchByteRange(0, 2) to BigInteger.ZERO, res)
    }

    @Test
    fun truncateUpperAndLowerBits() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            1, 3, shiftToTop(
                BigInteger("ffaabbccee", 16)
            ).lift(), nullNext
        )
        Assertions.assertEquals(ScratchByteRange(0, 2) to BigInteger("aabbcc", 16), res)
    }

    private val upperBound = 0xef.toBigInteger()

    private val lowerBound = BigInteger.ZERO

    @Test
    fun nonConstantWithAllZeroPrefix() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            28, 2, toConstantPrefix(
                upperBound, lowerBound, upperBound
            ), nullNext
        )
        Assertions.assertEquals(ScratchByteRange(0, 1) to BigInteger.ZERO, res)
    }

    @Test
    fun nonConstantWithConstantPrefix() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            29, 2, toConstantPrefix(
                // index in the final byte vector:
                //28 29 30
                0xee_00_eb.toBigInteger(), lowerBound, upperBound
            ), nullNext
        )
        Assertions.assertEquals(ScratchByteRange(0, 1) to 0xeb.toBigInteger(), res)
    }

    @Test
    fun nonConstantWithZeroPrefix() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            25, 6, toConstantPrefix(
                0x7b.toBigInteger(), lowerBound, upperBound
            ), nullNext
        )
        Assertions.assertEquals(ScratchByteRange(0, 5) to 0x7b.toBigInteger(), res)
    }

    @Test
    fun nonConstantDivergeMidByte() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            30, 2, toConstantPrefix(
                0x7b.toBigInteger(), 0xea.toBigInteger(), 0xef.toBigInteger()
            ), nullNext
        )
        Assertions.assertEquals(ScratchByteRange(0, 0) to 0x7b.toBigInteger(), res)
    }

    @Test
    fun testNonConstantPrefix() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            31, 1, IntValue.Interval(lb = BigInteger.ZERO, ub = 28.toBigInteger()), nullNext
        )
        Assertions.assertNull(res)
    }

    @Test
    fun testMultiWordConstant() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            29, 5, 0xffeeaa.lift()
        ) { ->
            shiftToTop(0xbbccee).lift()
        }
        Assertions.assertEquals(ScratchByteRange(0, 4) to 0xffeeaabbcc.toBigInteger(), res)
    }

    @Test
    fun testMultiWordNondetSecondWord() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            29, 5, 0xffeeaa.lift()
        ) {
            IntValue.Nondet
        }
        Assertions.assertEquals(ScratchByteRange(0, 2) to 0xffeeaa.toBigInteger(), res)
    }

    @Test
    fun testConstantPrefixConstantSecondWord() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            30, 3, toConstantPrefix(
                0xef, 0, 0x7
            )
        ) { -> shiftToTop(0xff).lift() }
        Assertions.assertEquals(ScratchByteRange(0, 0) to 0xef.toBigInteger(), res)
    }

    @Test
    fun testConstantWithConstantPrefixSecondWord() {
        val res = CallGraphBuilder.extractConstructorSignatureFromConst(
            29, 6, 0xffaaee.lift()
        ) {
            toConstantPrefix(0xeeaa, 0x7, 0xbe, 29)
        }
        Assertions.assertEquals(ScratchByteRange(0, 4) to 0xffaaeeeeaa.toBigInteger(), res)
    }
}