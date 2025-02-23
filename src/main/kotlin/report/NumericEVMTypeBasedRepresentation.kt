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

package report

import spec.cvlast.typedescriptors.VMNumericValueTypeDescriptor
import spec.cvlast.typedescriptors.VMTypeDescriptor
import spec.cvlast.typedescriptors.VMUnsignedNumericValueTypeDescriptor
import spec.cvlast.typedescriptors.VMValueTypeDescriptor
import utils.SignUtilities.from2sComplement
import java.math.BigInteger

enum class NumType {
    NonNegative, Signed, TwosCompliment
}

/**
 * Displays numeric values, based on their evm type.
 * This means, that redundant bits will be removed,
 * and for signed values, twos complement will be calculated if needed
 * depends on their NumType.
 * For example, we do not want to display uint8 value with more
 * than 8 bits, and we should consider the twos complement method
 * (for some signed value).
 */
object NumericEVMTypeBasedRepresentation {

    /**
     * Shows only relevant bits of the value [input] (LSBs).
     * [n] - The number of bits to cast.
     * [numType] - Enum value represent whether the input number is positive only, signed or two's compliment.
     * [input] - The input number.
     */
    fun bitsToDisplay(input: BigInteger, n: Int, numType: NumType): BigInteger {
        /** Computes Twos Complement for signed values */
        fun twosComplement(input: BigInteger, n: Int): BigInteger {
            // First power out of number range
            val powerN = 2.toBigInteger().pow(n)
            val mask = powerN - BigInteger.ONE
            val possibleRet = input.and(mask)
            return possibleRet.from2sComplement()
        }

        return when (numType) {
            NumType.NonNegative -> {
                // Report if input is out of the positive integer limits; return input
                /* TODO: comment in this check after fixing the bugs of the regtest that fails here.
                    check(input >= BigInteger.ZERO && input <= SignUtilities.maxUnsignedValueOfBitwidth(n)) {
                    "Display input $input is out of bounds of 0 to 2^n, n=$n"}*/
                input
            }

            NumType.Signed -> {
                // Report if input is out the signed integer limits; return input
                /* TODO: comment in this check after fixing the bugs of the regtest that fails here.
                    check(input >= SignUtilities.minSignedValueOfBitwidth(n) &&
                    input <= SignUtilities.maxSignedValueOfBitwidth(n)) {
                    "Display input $input is out of bounds of -2^(n-1) to 2^(n-1) - 1, n=$n"}*/
                input
            }

            NumType.TwosCompliment -> twosComplement(input, n)
        }
    }

    /**
     *  Filters irrelevant bits based on the evm type [type].
     * For illegal evm types (not pointers to offsets or actual numeric values),
     * an exception is thrown.
     */
    fun convertByType(input: BigInteger, descriptor: VMTypeDescriptor?): BigInteger {
        return if (descriptor == null) {
            input
        } else {
            if (descriptor is VMNumericValueTypeDescriptor) {
                if (descriptor is VMUnsignedNumericValueTypeDescriptor) {
                    bitsToDisplay(
                        input, numType = NumType.NonNegative, n = descriptor.bitwidth
                    )
                } else {
                    bitsToDisplay(
                        input = input, numType = NumType.TwosCompliment, n = descriptor.bitwidth
                    )
                }
            } else if (descriptor is VMValueTypeDescriptor) {
                bitsToDisplay(input = input, numType = NumType.TwosCompliment, n = descriptor.bitwidth)
            } else {
                input
            }
        }
    }
}
