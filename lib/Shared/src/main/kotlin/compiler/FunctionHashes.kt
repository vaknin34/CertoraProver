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

package compiler

import kotlinx.serialization.Serializable
import org.komputing.khash.keccak.Keccak
import org.komputing.khash.keccak.KeccakParameter
import utils.*
import java.math.BigInteger
import java.util.*

@Serializable
data class SolidityFunctionParam(val name : String = "", val type : String)



/**
 * [https://solidity.readthedocs.io/en/develop/abi-spec.html?highlight=stateMutability#json]
 *  and [https://solidity.readthedocs.io/en/develop/contracts.html#pure-functions]
 */
@Serializable
enum class SolidityFunctionStateMutability(val keyword: String, val isPure: Boolean, val isView: Boolean,
                                           val isPayable: Boolean) {
    nonpayable("nonpayable", false, false, false),
    payable("payable", false, false, true),
    pure("pure", true, true, false),
    view("view", false, true, false),
    ;

    companion object {
        private val stringToValue = values().associate { v -> (v.keyword to v) }


        fun fromString(s: String) = stringToValue[s] ?: error("not a valid state mutability")

        val Default = nonpayable // TODO: Default should allow for both "view" and "non view", "pure" and "non pure" (how to encode that pure is also view?)
    }
}

/**
 * @param definitelyNonPayable Explanation of naming:
 *    - negation: "non-payable" is the default
 *    - "definitely" - because it's a default that restricts the inputs, so I see this as a bit of a dangerous default.
 *                      If we don't know for sure that the function is nonpayable, I'd rather treat it as payable.
 *                      (explanation from shelly)
 */
@Serializable
data class SolidityFunction(val name : String,
                            val args : List<SolidityFunctionParam>,
                            val hash : String,
                            val definitelyNonPayable : Boolean,
                            val isConstant: Boolean,
                            val outputs : List<SolidityFunctionParam>,
                            val stateMutability: SolidityFunctionStateMutability
                            )

fun calculateHash(abi : ABI) : String {
    val name = abi.name
    val inputTypes = abi.inputs.map { it.type }
    return calculateHashFromNameAndArgTypes(name,inputTypes)
}

// TODO: change from String to BigInteger
fun calculateHashFromNameAndArgTypes(name : String, argTypes : List<String>) : String {
    val stringToHash = "$name(${argTypes.joinToString(",")})"
    val hash = Keccak.digest(stringToHash.toByteArray(), KeccakParameter.KECCAK_256)
    return hash.take(4).toHexString()
}

@Deprecated("probably shouldn't be used; we are computing sighashes on python level (stored in " +
        "certora_build.json), so this is duplicate functionality")
fun calculateHashFromCanonicalName(canonicalName: String): String {
    val hash = Keccak.digest(canonicalName.toByteArray(), KeccakParameter.KECCAK_256)
    return hash.take(4).toHexString()
}

@Deprecated("probably shouldn't be used; we are computing sighashes on python level (stored in " +
        "certora_build.json), so this is duplicate functionality")
fun calculateHashFromCanonicalNameBigInt(canonicalName: String): BigInteger =
        @Suppress("deprecation")
        calculateHashFromCanonicalName(canonicalName).toBigInteger(16)

fun applyKeccakList(words: List<BigInteger>): BigInteger {
    val input = words.map {
        it.toByteArray().let { ba ->
            // if we have 2^256-1, it will have 33 bytes (the first is a 0). Last byte is LSB.
            val lsbs = ba.takeLast(Math.min(ba.size, 32))
            if (lsbs.size <= 32) {
                val byteArray = ByteArray(32 - lsbs.size) // extend with 0's
                byteArray + lsbs.toByteArray()
            } else {
                lsbs.toByteArray()
            }
        }
    }.reduce { x, y -> x + y }
    return applyKeccak(input)
}

fun applyKeccak(vararg words: BigInteger): BigInteger = applyKeccakList(words.toList())

fun applyKeccakByHexStringConversion(vararg words: BigInteger): BigInteger {
    // encode each big int as a hex string (32 bytes are 64 bytes of a hex string)
    val str = words.joinToString("") { String.format(Locale.ROOT, "%064x", it) }
    return applyKeccak(hexStringToBytes(str))
}

fun applyKeccak(byteArray: ByteArray) =
    Keccak.digest(byteArray, KeccakParameter.KECCAK_256) // get a bytearray for the hash
        .joinToString("") {  String.format(Locale.ROOT, "%02x", (it.toInt() and 0xFF)) }.toBigInteger(16) // convert it to a biginteger

fun applyKeccak(byteArray: List<UByte>) = applyKeccak(byteArray.toByteArray())
