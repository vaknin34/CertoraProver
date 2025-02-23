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

package spec.converters

import analysis.CommandWithRequiredDecls
import analysis.merge
import datastructures.stdcollections.*
import evm.EVM_WORD_SIZE
import evm.EVM_WORD_SIZE_INT
import spec.cvlast.typedescriptors.IMappingKeyOutput
import spec.cvlast.typedescriptors.IStorageMapping
import tac.CallId
import tac.DataField
import tac.Tag
import vc.data.*

/**
 * Wrapper class that combines the code to do the mapping key computation, and the variable which holds that result [output].
 * [indexVar] gives the variable that should be used as the key into the map; this is usually the input variable, except
 * for bytes keys, where the key is hashed (which matches how we annotate keys for solidity based map lookups)
 */
data class EVMMappingKeyOutput(val crd: CommandWithRequiredDecls<TACCmd.Spec>, val output: TACSymbol.Var, val indexVar: TACSymbol.Var) : IMappingKeyOutput

/**
 * "Input" class which is the distinguished implementation for [IStorageMapping] on the EVM for converting values
 * to mapping keys. This class' state holds the slot of the mapping being keyed into, as well as the call id
 * of the overall access operation. Its methods provide the logic for the different keying operations.
 */
class EVMStorageMapping(val callId: CallId, private val mappingSlot: TACSymbol) : IStorageMapping {
    /**
     * Used with [v] holds the result of a hash blob. In this case, performing the keying operation requires reversing
     * the hash operation. Normally this would be impossible in concrete execution,
     * but given the model of the hash as just an injective function on a buffer, it is actually very easy to do symbolically.
     *
     * Effectively, given a variable v which holds the result of hashing some bytes buffer b, we reconstruct the original buffer b,
     * and then compute the mapping offset as follows:
     * ```
     * buffer = *
     * len = *
     * require(hash(buffer, len) == v)
     * buffer[len] = slot
     * result = hash(buffer, len + 32)
     * ```
     */
    fun hashBlobKey(v: TACSymbol.Var) : EVMMappingKeyOutput {
        /**
         * Holds the the non-deterministic buffer which we will constrain to hash the same as [v]
         */
        val havocBuffer = TACKeyword.TMP(Tag.ByteMap, "!nondetBuffer").toUnique("!").at(callId)

        /**
         * The length of this non-deterministic buffer.
         */
        val havocLength = TACKeyword.TMP(Tag.Bit256, "!nondetLength").toUnique("!").at(callId)

        /**
         * The result of hashing havocBuffer, we constrain this to be equal to v, i.e., havocBuffer will
         * be equal to the buffer that produced v.
         */
        val reversedHash = TACKeyword.TMP(Tag.Bit256, "!reversedHashResult").toUnique("!").at(callId)

        /**
         * The result of hash(havocBuffer, havocLength) == v (which we will assume to be true)
         */
        val compResult = TACKeyword.TMP(Tag.Bool, "!comp").toUnique("!").at(callId)

        /**
         * The length of the hash for the map access.
         */
        val totalLength = TACKeyword.TMP(Tag.Bit256, "!totalLen").toUnique("!").at(callId)

        /**
         * The result of the hash
         */
        val resultVar = TACKeyword.TMP(Tag.Bit256, "!keyResult").toUnique("!").at(callId)

        val res = CommandWithRequiredDecls(listOf(
            /**
             * buffer = *
             */
            TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                lhs = havocBuffer
            ),
            /**
             * len = *
             */
            TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                lhs = havocLength
            ),
            /**
             * reversedHash = hash(buffer, len)
             */
            TACCmd.Simple.AssigningCmd.AssignSha3Cmd(
                lhs = reversedHash,
                op1 = TACSymbol.Zero,
                op2 = havocLength,
                memBaseMap = havocBuffer
            ),
            /**
             * compResult = v == reversedHash
             */
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = compResult,
                rhs = TACExpr.BinRel.Eq(
                    reversedHash.asSym(),
                    v.asSym()
                )
            ),
            /**
             * assume compResult
             */
            TACCmd.Simple.AssumeCmd(
                compResult
            ),
            /**
             * `buffer[len] = mappingSlot`
             */
            TACCmd.Simple.AssigningCmd.ByteStore(
                base = havocBuffer,
                loc = havocLength,
                value = mappingSlot
            ),
            /**
             * totalLength = len + 32
             */
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = totalLength,
                rhs = TACExpr.Vec.Add(
                    havocLength.asSym(),
                    EVM_WORD_SIZE.asTACExpr
                )
            ),
            /**
             * resultVar = hash(buffer, totalLength)
             */
            TACCmd.Simple.AssigningCmd.AssignSha3Cmd(
                lhs = resultVar,
                memBaseMap = havocBuffer,
                op1 = TACSymbol.Zero,
                op2 = totalLength
            )
        ), setOfNotNull(resultVar, havocBuffer, totalLength, compResult, v, reversedHash, havocLength, mappingSlot as? TACSymbol.Var))
        return EVMMappingKeyOutput(
            crd = res,
            output = resultVar,
            indexVar = v
        )
    }

    /**
     * Handle a mapping key that is a bytes/string array that is NOT in bytes blob form. This is significantly simpler, as
     * we do not need to symbolically reverse the hash. [v] is expected to be a CVL bytes/string array.
     */
    fun hashBytesKey(v: TACSymbol.Var) : EVMMappingKeyOutput {
        /**
         * This implementation generates code that effectively does the following:
         * ```
         * buffer = *
         * copy(buffer, 0, v, 0, v.length)
         * buffer[v.length] = mappingSlot
         * result = hash(buffer, v.length + 32)
         * ```
         *
         * where the `copy` operation copies to the first argument data from the 3rd argument.
         */

        /**
         * the variable corresponding to `buffer` in the above.
         */
        val hashKeyBuffer = TACKeyword.TMP(Tag.ByteMap, "!buffer").toUnique("!").at(callId)

        /**
         * The length of the array in `v` (i.e., this will hold v.length)
         */
        val hashKeyLength = TACKeyword.TMP(Tag.Bit256, "!keyLength").toUnique("!").at(callId)

        /**
         * The length of the entire buffer for hashing, namely, `v.length + 32`.
         */
        val totalLength = TACKeyword.TMP(Tag.Bit256, "!totalLength").toUnique("!").at(callId)

        /**
         * The result of the hash operation, aka `result` in the above pseudo-code
         */
        val result = TACKeyword.TMP(Tag.Bit256, "!key").toUnique("!").at(callId)

        val keyHash = TACKeyword.TMP(Tag.Bit256, "!keyHash").toUnique("!").at(callId)

        check(v.tag is Tag.CVLArray)
        val code = CommandWithRequiredDecls(listOf(
            /**
             * hashKeyLength = v.length
             */
            TACCmd.CVL.ArrayLengthRead(
                lhs = hashKeyLength,
                rhs = v
            ),
            /**
             * hashKeyBuffer = *
             */
            TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                lhs = hashKeyBuffer
            ),
            /**
             * The copy operation in the above.
             */
            TACCmd.CVL.ArrayCopy(
                dst = TACCmd.CVL.BufferPointer(
                    offset = TACSymbol.Zero,
                    buffer = TACCmd.CVL.Buffer.EVMBuffer(hashKeyBuffer)
                ),
                src = TACCmd.CVL.BufferPointer(
                    offset = TACSymbol.Zero,
                    buffer = TACCmd.CVL.Buffer.CVLBuffer(
                        v,
                        dataPath = listOf(DataField.ArrayData)
                    )
                ),
                elementSize = 1,
                logicalLength = hashKeyLength
            ),
            /**
             * totalLength = hashKeyLength + 32, AKA v.length + 32
             */
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = totalLength,
                rhs = TACExpr.Vec.Add(
                    hashKeyLength.asSym(),
                    EVM_WORD_SIZE.asTACExpr
                )
            ),
            /**
             * `hashKeyBuffer[hashKeyLength] = mappingSlot`
             */
            TACCmd.Simple.AssigningCmd.ByteStore(
                base = hashKeyBuffer,
                loc = hashKeyLength,
                value = mappingSlot
            ),
            /**
             * result = hash(hashKeyBuffer, totalLength)
             */
            TACCmd.Simple.AssigningCmd.AssignSha3Cmd(
                lhs = result,
                op1 = TACSymbol.Zero,
                op2 = totalLength,
                memBaseMap = hashKeyBuffer
            ),
            TACCmd.Simple.AssigningCmd.AssignSha3Cmd(
                lhs = keyHash,
                op1 = TACSymbol.Zero,
                op2 = hashKeyLength,
                memBaseMap = hashKeyBuffer
            )
        ), setOfNotNull(result, totalLength, hashKeyBuffer, hashKeyLength, mappingSlot as? TACSymbol.Var, keyHash))
        return EVMMappingKeyOutput(
            crd = code,
            output = result,
            indexVar = keyHash
        )
    }

    /**
     * The simplest version, hash a mapping key [v] that fits within a single word. This just uses the [vc.data.TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd]
     * command and doesn't have to futz around with buffers. However, the encoding of the CVL type used must be consistent
     * with what *would* be placed into an EVM buffer; this encoding is determiend by the [bitEncoding] argument.
     */
    fun hashPrimitiveKey(v: TACSymbol.Var, bitEncoding: Tag.CVLArray.UserArray.ElementEncoding) : EVMMappingKeyOutput {
        /**
         * Variable holding the result of the hash
         */
        val output = TACKeyword.TMP(Tag.Bit256, "!hashResult").toUnique("!").at(callId)

        /**
         * Variable holding the EVM encoded version of the key
         */
        val bitValue = TACKeyword.TMP(Tag.Bit256, "!nativeRepr").toUnique("!").at(callId)

        /**
         * Convert to the EVM encoding according to [bitEncoding]
         */
        val conversionCode = EVMMoveSemantics.ValueConverters.convertValueTypeToEncoding(
            src = v,
            dest = bitValue,
            destEncoding = bitEncoding
        )

        /**
         * And then hash the EVM version of [v] and place it in output.
         */
        val hashingCode = CommandWithRequiredDecls(listOf(
            TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd(
                length = (EVM_WORD_SIZE_INT * 2).asTACSymbol(),
                lhs = output,
                args = listOf(bitValue, mappingSlot)
            )
        ), setOfNotNull(output, bitValue, mappingSlot as? TACSymbol.Var))
        return EVMMappingKeyOutput(
            crd = conversionCode.merge(hashingCode),
            output = output,
            indexVar = v
        )
    }
}
