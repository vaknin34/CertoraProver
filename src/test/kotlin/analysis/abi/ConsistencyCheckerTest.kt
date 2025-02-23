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

package analysis.abi

import analysis.pta.HeapType
import analysis.pta.abi.DecoderAnalysis
import evm.EVM_WORD_SIZE
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.math.BigInteger

class ConsistencyCheckerTest {
    @Test
    fun testComplicatedStriding() {
        val bufferStart = DecoderAnalysis.BufferAccessPath.Deref(DecoderAnalysis.BufferAccessPath.Offset(
                offset = 4.toBigInteger(),
                base = DecoderAnalysis.BufferAccessPath.Root
        ))
        val writeObject = DecoderAnalysis.BufferObject.Struct(
                contents = DecoderAnalysis.BufferObject.Struct.StructContents(
                        fields = mapOf(
                                BigInteger.ZERO to DecoderAnalysis.BufferObject.Word(setOf(
                                        DecoderAnalysis.BufferAccessPath.Offset(
                                                offset = BigInteger.ZERO,
                                                base = bufferStart
                                        )
                                )),
                                /*
                                   B[3]
                                 */
                                EVM_WORD_SIZE to DecoderAnalysis.BufferObject.Struct(
                                        contents = DecoderAnalysis.BufferObject.Struct.StructContents(
                                                fields = mapOf(
                                                        /* First field of B[3] */
                                                        BigInteger.ZERO to DecoderAnalysis.BufferObject.Struct(
                                                                DecoderAnalysis.BufferObject.Struct.StructContents(
                                                                        fields = mapOf(
                                                                                /* padding fields */
                                                                                BigInteger.ZERO to DecoderAnalysis.BufferObject.Word(setOf(
                                                                                        DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                offset = EVM_WORD_SIZE,
                                                                                                base = bufferStart
                                                                                        )
                                                                                )),
                                                                                EVM_WORD_SIZE to DecoderAnalysis.BufferObject.Word(setOf(
                                                                                        DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                offset = 64.toBigInteger(),
                                                                                                base = bufferStart
                                                                                        )
                                                                                )),
                                                                                /* C[5] field of first element of B[3] (begins at offset 96) */
                                                                                64.toBigInteger() to DecoderAnalysis.BufferObject.Struct(
                                                                                        contents = DecoderAnalysis.BufferObject.Struct.StructContents(
                                                                                                fields = mapOf(
                                                                                                        /* first element of first C[5] of first B[3] */
                                                                                                        BigInteger.ZERO to DecoderAnalysis.BufferObject.Struct(
                                                                                                                contents = DecoderAnalysis.BufferObject.Struct.StructContents(
                                                                                                                        /* padding field of C */
                                                                                                                        fields = mapOf(BigInteger.ZERO to DecoderAnalysis.BufferObject.Word(setOf(
                                                                                                                                DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                        offset = 96.toBigInteger(),
                                                                                                                                        base = bufferStart
                                                                                                                                )
                                                                                                                        )),
                                                                                                                                /* uint[3] of first C of first B */
                                                                                                                                EVM_WORD_SIZE to DecoderAnalysis.BufferObject.Struct(
                                                                                                                                        DecoderAnalysis.BufferObject.Struct.StructContents(
                                                                                                                                                fields = mapOf(
                                                                                                                                                        /* first element of uint[3] */
                                                                                                                                                        BigInteger.ZERO to DecoderAnalysis.BufferObject.Word(setOf(
                                                                                                                                                                DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                                                        offset = 128.toBigInteger(),
                                                                                                                                                                        base = bufferStart
                                                                                                                                                                )
                                                                                                                                                        ))
                                                                                                                                                ),
                                                                                                                                                /* remaining elements of uint[3] */
                                                                                                                                                static = DecoderAnalysis.BufferObject.Word(setOf(
                                                                                                                                                        DecoderAnalysis.BufferAccessPath.StaticStride(
                                                                                                                                                                strideBy = EVM_WORD_SIZE,
                                                                                                                                                                parent = DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                                                        offset = 128.toBigInteger(),
                                                                                                                                                                        base = bufferStart
                                                                                                                                                                )
                                                                                                                                                        )
                                                                                                                                                ))
                                                                                                                                        )
                                                                                                                                )
                                                                                                                        ),
                                                                                                                        static = null
                                                                                                                )
                                                                                                        )
                                                                                                ),
                                                                                                /* remaining elements of C[5] in FIRST B of B[3] */
                                                                                                static = DecoderAnalysis.BufferObject.Struct(
                                                                                                        DecoderAnalysis.BufferObject.Struct.StructContents(
                                                                                                                /* This is a summary of all instances C's in C[5], so we have a offset field 0*/
                                                                                                                fields = mapOf(
                                                                                                                        BigInteger.ZERO to DecoderAnalysis.BufferObject.Word(setOf(
                                                                                                                                // C's are 128 bytes large
                                                                                                                                DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                        offset = BigInteger.ZERO,
                                                                                                                                        base = DecoderAnalysis.BufferAccessPath.StaticStride(
                                                                                                                                                strideBy = 128.toBigInteger(),
                                                                                                                                                parent = DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                                        // remember: the C5's begin at 96
                                                                                                                                                        offset = 96.toBigInteger(),
                                                                                                                                                        base = bufferStart
                                                                                                                                                )
                                                                                                                                        ))
                                                                                                                        )),
                                                                                                                        EVM_WORD_SIZE to DecoderAnalysis.BufferObject.Struct(
                                                                                                                                /*
                                                                                                                                   The uint[3] in each C. We (should) know at this point that they are tuples, no fields
                                                                                                                                 */
                                                                                                                                contents = DecoderAnalysis.BufferObject.Struct.StructContents(
                                                                                                                                        fields = mapOf(),
                                                                                                                                        static = DecoderAnalysis.BufferObject.Word(setOf(
                                                                                                                                                /* The fields of these uint[3]'s are touched by */
                                                                                                                                                DecoderAnalysis.BufferAccessPath.StaticStride(
                                                                                                                                                        /* stepping by 32 bytes... */
                                                                                                                                                        EVM_WORD_SIZE,
                                                                                                                                                        parent = DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                                                /* starting from the 32 bytes offset from ... */
                                                                                                                                                                offset = EVM_WORD_SIZE,
                                                                                                                                                                base = DecoderAnalysis.BufferAccessPath.StaticStride(
                                                                                                                                                                        /* stepping by 128 bytes ... */
                                                                                                                                                                        strideBy = 128.toBigInteger(),
                                                                                                                                                                        /* starting from the beginning of the C5's (aka 96) */
                                                                                                                                                                        parent = DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                                                                offset = 96.toBigInteger(),
                                                                                                                                                                                base = bufferStart
                                                                                                                                                                        )
                                                                                                                                                                )
                                                                                                                                                        )
                                                                                                                                                )
                                                                                                                                        ))
                                                                                                                                )
                                                                                                                        )
                                                                                                                ),
                                                                                                                /* not a tuple */
                                                                                                                static = null
                                                                                                        )
                                                                                                )
                                                                                        )

                                                                                )

                                                                        ),
                                                                        static = null /* not a tuple */
                                                                )
                                                        )
                                                ),
                                                /* summary of all B's in the outer B[3] */
                                                static = DecoderAnalysis.BufferObject.Struct(
                                                        contents = DecoderAnalysis.BufferObject.Struct.StructContents(
                                                                /* the first two fields of every b3 are at static offsets */
                                                                fields = mapOf(
                                                                        BigInteger.ZERO to DecoderAnalysis.BufferObject.Word(setOf(
                                                                                /*
                                                                                   The pad1 field here lies at the first byte of each B, which is given by striding by 704 bytes starting from the beginning
                                                                                   of B[3], aka 32
                                                                                 */
                                                                                DecoderAnalysis.BufferAccessPath.Offset(
                                                                                        offset = BigInteger.ZERO,
                                                                                        base = DecoderAnalysis.BufferAccessPath.StaticStride(
                                                                                                strideBy = 704.toBigInteger(),
                                                                                                parent = DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                        offset = EVM_WORD_SIZE,
                                                                                                        base = bufferStart
                                                                                                )
                                                                                        )
                                                                                ))),
                                                                        EVM_WORD_SIZE to DecoderAnalysis.BufferObject.Word(setOf(
                                                                                DecoderAnalysis.BufferAccessPath.Offset(
                                                                                        offset = EVM_WORD_SIZE,
                                                                                        base = DecoderAnalysis.BufferAccessPath.StaticStride(
                                                                                                strideBy = 704.toBigInteger(),
                                                                                                parent = DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                        offset = EVM_WORD_SIZE,
                                                                                                        base = bufferStart
                                                                                                )
                                                                                        )
                                                                                )
                                                                        )),
                                                                        /* the c[5] field (which begins offset 64 from each B */
                                                                        64.toBigInteger() to DecoderAnalysis.BufferObject.Struct(
                                                                                contents = DecoderAnalysis.BufferObject.Struct.StructContents(
                                                                                        /* these are known to be tuples */
                                                                                        fields = mapOf(),
                                                                                        /* summary of all C's in the tuple */
                                                                                        static = DecoderAnalysis.BufferObject.Struct(
                                                                                                DecoderAnalysis.BufferObject.Struct.StructContents(
                                                                                                        fields = mapOf(
                                                                                                                BigInteger.ZERO to DecoderAnalysis.BufferObject.Word(setOf(
                                                                                                                        /* this gets fun. The first padding field of each C is reachable by */
                                                                                                                        DecoderAnalysis.BufferAccessPath.Offset(base = DecoderAnalysis.BufferAccessPath.StaticStride(
                                                                                                                                /* stepping 128 bytes (the size of each C) */
                                                                                                                                strideBy = 128.toBigInteger(),
                                                                                                                                parent = DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                        /* starting from 64 bytes within each B */
                                                                                                                                        offset = 64.toBigInteger(),
                                                                                                                                        /* which are reachable by stepping 704 bytes (the size of each B) */
                                                                                                                                        base = DecoderAnalysis.BufferAccessPath.StaticStride(
                                                                                                                                                strideBy = 704.toBigInteger(),
                                                                                                                                                /* starting from 32 bytes within the A struct */
                                                                                                                                                parent = DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                                        offset = EVM_WORD_SIZE,
                                                                                                                                                        base = bufferStart
                                                                                                                                                )
                                                                                                                                        )
                                                                                                                                )
                                                                                                                        ), offset = BigInteger.ZERO)
                                                                                                                )),
                                                                                                                EVM_WORD_SIZE to DecoderAnalysis.BufferObject.Struct(
                                                                                                                        DecoderAnalysis.BufferObject.Struct.StructContents(
                                                                                                                                fields = mapOf(),
                                                                                                                                static = DecoderAnalysis.BufferObject.Word(setOf(
                                                                                                                                        DecoderAnalysis.BufferAccessPath.Offset(base = DecoderAnalysis.BufferAccessPath.StaticStride(
                                                                                                                                                strideBy = EVM_WORD_SIZE,
                                                                                                                                                parent = DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                                        offset = EVM_WORD_SIZE,
                                                                                                                                                        base = DecoderAnalysis.BufferAccessPath.StaticStride(
                                                                                                                                                                /* stepping 128 bytes (the size of each C) */
                                                                                                                                                                strideBy = 128.toBigInteger(),
                                                                                                                                                                parent = DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                                                        /* starting from 64 bytes within each B */
                                                                                                                                                                        offset = 64.toBigInteger(),
                                                                                                                                                                        /* which are reachable by stepping 704 bytes (the size of each B) */
                                                                                                                                                                        base = DecoderAnalysis.BufferAccessPath.StaticStride(
                                                                                                                                                                                strideBy = 704.toBigInteger(),
                                                                                                                                                                                /* starting from 32 bytes within the A struct */
                                                                                                                                                                                parent = DecoderAnalysis.BufferAccessPath.Offset(
                                                                                                                                                                                        offset = EVM_WORD_SIZE,
                                                                                                                                                                                        base = bufferStart
                                                                                                                                                                                )
                                                                                                                                                                        )
                                                                                                                                                                )
                                                                                                                                                        )
                                                                                                                                                )
                                                                                                                                        ), offset = BigInteger.ZERO)
                                                                                                                                ))
                                                                                                                        )
                                                                                                                )
                                                                                                        ),
                                                                                                        static = null
                                                                                                )
                                                                                        )
                                                                                )
                                                                        )
                                                                ),
                                                                static = null
                                                        )
                                                )
                                        )
                                )
                        ),
                        static = null
                )
        )

        val uint3Type = HeapType.OffsetMap(
                fieldTypes = mapOf(
                        BigInteger.ZERO to HeapType.Int,
                        EVM_WORD_SIZE to HeapType.Int,
                        64.toBigInteger() to HeapType.Int
                ),
                sz = 96.toBigInteger(),
                true
        )
        val structCType = HeapType.OffsetMap(
                fieldTypes = mapOf(
                        BigInteger.ZERO to HeapType.Int,
                        EVM_WORD_SIZE to uint3Type
                ),
                sz = 64.toBigInteger(),
                true
        )
        val c5TupleType = HeapType.OffsetMap(
                fieldTypes = (0..4).associate {
                    (it.toBigInteger() * EVM_WORD_SIZE) to structCType
                },
                sz = 5.toBigInteger() * EVM_WORD_SIZE,
                true
        )
        val structBType = HeapType.OffsetMap(
                fieldTypes = mapOf(
                        BigInteger.ZERO to HeapType.Int,
                        EVM_WORD_SIZE to HeapType.Int,
                        64.toBigInteger() to c5TupleType
                ),
                sz = 96.toBigInteger(),
                true
        )
        val b3TupleType = HeapType.OffsetMap(
                fieldTypes = (0..2).associate {
                    (it.toBigInteger() * EVM_WORD_SIZE) to structBType
                },
                sz = EVM_WORD_SIZE * 3.toBigInteger(),
                true
        )
        val structAType = HeapType.OffsetMap(
                fieldTypes = mapOf(
                        BigInteger.ZERO to HeapType.Int,
                        EVM_WORD_SIZE to b3TupleType
                ),
                sz = 64.toBigInteger(),
                true
        )
        Assertions.assertNotNull(DecoderAnalysis.checkConsistency(structAType, writeObject, DecoderAnalysis.PathProcess.Root))
    }
}