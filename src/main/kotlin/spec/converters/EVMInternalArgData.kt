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
import analysis.ip.InternalArgSort
import analysis.ip.InternalFuncArg
import analysis.ip.InternalFuncValueLocation
import analysis.merge
import analysis.pta.abi.PartitionField
import datastructures.stdcollections.*
import evm.EVM_WORD_SIZE
import spec.SafeMathCodeGen
import spec.converters.repr.ArrayWriter
import spec.converters.repr.CVLDataOutput
import spec.converters.repr.StructWriter
import spec.cvlast.typedescriptors.DecoderLayout
import spec.cvlast.typedescriptors.EVMTypeDescriptor
import spec.toProg
import tac.Tag
import utils.CertoraInternalErrorType
import utils.CertoraInternalException
import vc.data.*
import java.math.BigInteger

@RequiresOptIn(
    level = RequiresOptIn.Level.ERROR,
    message = "Exposed for converter tests"
)
annotation class ConverterTestOnly

sealed class EVMInternalCalldataArg(
    protected val buffer: TACSymbol.Var,
    protected val scalars: Map<BigInteger, TACSymbol.Var>,
    private val calldataSize: TACSymbol.Var
) : EVMTypeDescriptor.EVMInternalSummaryInput, SafeMathCodeGen {
    fun decodeTo(
        output: CVLDataOutput,
        layout: DecoderLayout,
    ) : CVLTACProgram {
        val (dec, setup) = this.getDecoder()
        return DecodingInterpreter.decode(
            target = output,
            layout = layout,
            l = dec,
            onDecode = { offsetWithinBuffer: TACSymbol.Var, size: TACSymbol ->
                val endLocation = TACKeyword.TMP(Tag.Bit256, "!endIndex").toUnique("!")
                val boundsCheck = TACKeyword.TMP(Tag.Bool, "!boundsCheck").toUnique("!")
                safeAdd(lhs = endLocation, offsetWithinBuffer, size).merge(
                    CommandWithRequiredDecls(listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            lhs = boundsCheck,
                            rhs = TACExpr.BinRel.Le(
                                endLocation.asSym(),
                                calldataSize.asSym()
                            )
                        ),
                        TACCmd.Simple.AssumeCmd(
                            cond = boundsCheck
                        )),
                        setOf(calldataSize, endLocation, boundsCheck)
                    )
                )
            }
        ).prependToBlock0(setup)
    }

    abstract fun getDecoder(): Pair<LowLevelDecoder, CommandWithRequiredDecls<TACCmd.Spec>>

    protected fun getRawDecoder(
        startPosition: TACSymbol.Var
    ) : Pair<LowLevelDecoder, CommandWithRequiredDecls<TACCmd.Spec>> {
        return LowLevelDecoder(
            buffer = buffer,
            offset = startPosition,
            scalars = scalars
        )
    }

    class DecomposedArrayPointers(
        private val lengthVar: TACSymbol.Var,
        private val elemPointerVar: TACSymbol.Var,
        buffer: TACSymbol.Var,
        scalars: Map<BigInteger, TACSymbol.Var>, calldataSize: TACSymbol.Var
    ) : EVMInternalCalldataArg(buffer, scalars, calldataSize) {
        override fun getDecoder(): Pair<LowLevelDecoder, CommandWithRequiredDecls<TACCmd.Spec>> {
            val encodedLength = TACKeyword.TMP(Tag.Bit256, "!encodedLength").toUnique("!")
            val startPosition = TACKeyword.TMP(Tag.Bit256, "!actualStart").toUnique("!")
            val offsetSanity = TACKeyword.TMP(Tag.Bool, "!offsetSanity").toUnique("!")
            val lengthSanity = TACKeyword.TMP(Tag.Bool, "!lengthSanity").toUnique("!")

            val offsetSetup = CommandWithRequiredDecls(listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = offsetSanity,
                    rhs = TACExpr.BinRel.Ge(
                        o1 = elemPointerVar.asSym(),
                        o2 = EVM_WORD_SIZE.asTACExpr()
                    )
                ),
                TACCmd.Simple.AssumeCmd(
                    cond = offsetSanity
                ),
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = startPosition,
                    rhs = TACExpr.BinOp.Sub(
                        o1 = elemPointerVar.asSym(),
                        o2 = EVM_WORD_SIZE.asTACExpr()
                    )
                ),
                TACCmd.Simple.AssigningCmd.ByteLoad(
                    lhs = encodedLength,
                    base = buffer,
                    loc = startPosition
                ),
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = lengthSanity,
                    rhs = TACExpr.BinRel.Eq(
                        encodedLength.asSym(),
                        lengthVar.asSym()
                    )
                ),
                TACCmd.Simple.AssertCmd(
                    o = lengthSanity,
                    "Sanity on calldata array length variable"
                )
            ), setOf(buffer, elemPointerVar, lengthVar, offsetSanity, startPosition, encodedLength, lengthSanity))

            val (dec, setup) = this.getRawDecoder(startPosition)
            return dec to offsetSetup.merge(setup)
        }
    }

    class BasicCalldataPointer(
        val pointer: TACSymbol.Var,
        buffer: TACSymbol.Var,
        scalars: Map<BigInteger, TACSymbol.Var>,
        calldataSize: TACSymbol.Var
    ) : EVMInternalCalldataArg(buffer, scalars, calldataSize) {
        override fun getDecoder(): Pair<LowLevelDecoder, CommandWithRequiredDecls<TACCmd.Spec>> {
            return this.getRawDecoder(pointer)
        }
    }
}

/**
 * Implementation that wraps the internal arguments to a function. Serves a dual purpose to [EVMInternalReturnData].
 *
 * Encapsulates a location in memory/variales, the expected shape of which is indicated by the expect* functions that
 * are called by the user. These implementations will throw an exception if the internal data of these objects
 * do not support the operations, e.g., attempting to use [expectArray] on an [EVMInternalArgData] that wraps a primitive
 * value.
 */
sealed interface EVMInternalArgData : EVMTypeDescriptor.EVMInternalSummaryInput {
    /**
     * Indicates that the value wrapped by this object is expected to hold a primitive, which should be decoded using
     * [enc] and cleaned according to [clean], and the result placed in [output].
     * The result of all of these operations are merged and returned in the [CommandWithRequiredDecls] object.
     */
    fun expectPrimitive(
        output: CVLDataOutput,
        enc: Tag.CVLArray.UserArray.ElementEncoding,
        clean: (TACSymbol.Var) -> Pair<TACSymbol.Var, CommandWithRequiredDecls<TACCmd.Spec>>
    ) : CVLTACProgram

    /**
     * Indicates that the value encapsulated by this object is expected to hold a struct pointer. Each field should be decoded using [f], which is passed
     * the location index of the field, the [CVLDataOutput] which should hold the decoded value of the field, and the [EVMInternalArgData] object
     * which encapsulates the EVM representation of the field value. [fieldNameToOrdinal] indicates the *ordinal* offset of field
     * f in EVM. Thus for `struct Foo { uint a; uint b; }` a will be mapped to 0, and b will be mapped to 1 (their offsets within
     * memory can be recovered by multiplying by the word size).
     */
    fun expectStruct(
        output: CVLDataOutput,
        fieldNameToOrdinal: Map<String, Int>,
        f: (ind: Int, fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ) : CVLTACProgram

    /**
     * Indicates that the value encapsulated by this object is expected to hold a static array with [numElements] elements,
     * whose CVL tag is given by [elementTag].
     * [f] is used to do element-wise copies from EVM. It is invoked for each individual element of the static array:
     * the first argument is the [CVLDataOutput] which should hold the result of decoding the element which is represented by the
     * second argument of type [EVMInternalArgData].
     */
    fun expectStaticArray(
        output: CVLDataOutput,
        numElements: BigInteger,
        elementTag: Tag,
        f: (fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ) : CVLTACProgram

    /**
     * Indicates that this object is expected to represent an array whose elements
     * are of size [eSize]. [output] is expected to point to an array.
     * [f] receives 4 arguments:
     * * a variable which holds the location in memory where the elements of this array begin
     * * The partition which holds the elements of the array
     * * The writer which is used for writing into [output], and
     * * A callback "gen" which, when given a variable that is expected to the hold
     * the value of some element of this array, produces an [EVMInternalArgData] which encapsulates that value
     */
    fun expectArray(
        output: CVLDataOutput,
        eSize: Int,
        f: (elemStart: TACSymbol, partition: TACSymbol.Var, writer: ArrayWriter, gen: (TACSymbol.Var) -> EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram

    companion object {
        /**
         * Lift [invArg] into an [EVMInternalArgData] depending on the location information.
         */
        operator fun invoke(
            invArg: InternalFuncArg,
            monolithicMemoryArray: TACSymbol.Var?
        ) : EVMInternalArgData {
            require(invArg.sort == InternalArgSort.SCALAR)
            if(invArg.s !is TACSymbol.Var) {
                check(invArg.s is TACSymbol.Const) {
                    "Broken type hierarchy for ${invArg.s}, expected a constant"
                }
                return ConstantArg(
                    const = invArg.s
                )
            }
            return when (invArg.location) {
                null -> {
                    if(monolithicMemoryArray == null) {
                        throw CertoraInternalException(
                            CertoraInternalErrorType.SUMMARY_INLINING,
                            "Cannot inline a summary without location information if we also have a null memory array"
                        )
                    }
                    UnsplitArg(
                        inputSym = invArg.s,
                        memoryArg = monolithicMemoryArray
                    )
                }
                is InternalFuncValueLocation.Scalar -> {
                    PrimitiveArg(
                        inputSym = invArg.s
                    )
                }

                is InternalFuncValueLocation.PointerWithFields -> {
                    ReferenceArg(
                        inputSym = invArg.s,
                        fields = invArg.location.layoutForFields
                    )
                }
                InternalFuncValueLocation.Pointer -> throw CertoraInternalException(
                    CertoraInternalErrorType.SUMMARY_INLINING,
                    "Unexpected form for internal argument"
                )
                is InternalFuncValueLocation.UnsplitPointer -> UnsplitArg(invArg.s, invArg.location.monolithicArray)
            }
        }

        @ConverterTestOnly
        fun forPrimitive(
            v: TACSymbol.Var
        ) : EVMInternalArgData = PrimitiveArg(v)

        @ConverterTestOnly
        fun forReference(
            v: TACSymbol.Var,
            fields: Map<PartitionField, InternalFuncValueLocation.PointerLayoutInfo>
        ) : EVMInternalArgData = ReferenceArg(
            inputSym = v, fields = fields
        )
    }
}

class ConstantArg(private val const: TACSymbol.Const) : EVMInternalArgData, PrimitiveHandlerMixin {
    override fun expectPrimitive(
        output: CVLDataOutput,
        enc: Tag.CVLArray.UserArray.ElementEncoding,
        clean: (TACSymbol.Var) -> Pair<TACSymbol.Var, CommandWithRequiredDecls<TACCmd.Spec>>
    ): CVLTACProgram {
        val sym = TACKeyword.TMP(Tag.Bit256, "!valueHolder").toUnique("!")
        return this.expectPrimitiveImpl(
            inputSym = sym,
            output = output,
            enc = enc,
            clean = clean
        ).prependToBlock0(
            CommandWithRequiredDecls(
                listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = sym,
                        rhs = const.asSym()
                    )
                ), setOf(sym)
        ))
    }

    override fun expectStruct(
        output: CVLDataOutput,
        fieldNameToOrdinal: Map<String, Int>,
        f: (ind: Int, fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        referenceTyError("struct")
    }

    override fun expectStaticArray(
        output: CVLDataOutput,
        numElements: BigInteger,
        elementTag: Tag,
        f: (fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        referenceTyError("static array")
    }

    override fun expectArray(
        output: CVLDataOutput,
        eSize: Int,
        f: (TACSymbol, TACSymbol.Var, ArrayWriter, (TACSymbol.Var) -> EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        referenceTyError("dynamic array")
    }

    private fun referenceTyError(ctxt: String) : Nothing {
        throw UnsupportedOperationException("Constant argument $const cannot be a $ctxt reference")
    }

}

private interface PrimitiveHandlerMixin {
    fun expectPrimitiveImpl(
        inputSym: TACSymbol.Var,
        output: CVLDataOutput,
        enc: Tag.CVLArray.UserArray.ElementEncoding,
        clean: (TACSymbol.Var) -> Pair<TACSymbol.Var, CommandWithRequiredDecls<TACCmd.Spec>>
    ): CVLTACProgram {
        val (sym, code) = clean(inputSym)
        return output.movePrimitive { p, ctxt ->
            code.merge(EVMMoveSemantics.ValueConverters.convertValueTypeToEncoding(
                p, src = sym, destEncoding = enc
            )).toProg("primitive move", ctxt)
        }
    }
}

private interface ReferenceHandlerMixin<T> {
    fun lookupBaseFor(
        partitionField: PartitionField
    ) : T?

    val T.partitionVar: TACSymbol.Var
    fun T.asRecursiveArg(nextField: TACSymbol.Var): EVMInternalArgData

    fun expectStructImpl(
        inputSym: TACSymbol.Var,
        output: CVLDataOutput,
        fieldNameToOrdinal: Map<String, Int>,
        f: (ind: Int, fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        return output.startStruct(object : StructWriter {
            override fun generateField(output: CVLDataOutput, fieldName: String, fieldIndex: Int): CVLTACProgram {
                /**
                 * Get the offset within the EVM struct for the field
                 */
                val offset = (fieldNameToOrdinal[fieldName]?.toBigInteger()
                    ?: throw IllegalStateException("Cannot find field $fieldName in EVM layout")) * EVM_WORD_SIZE

                /**
                 * Variable to hold the field pointer
                 */
                val fldPointer = TACKeyword.TMP(Tag.Bit256, "!field!${fieldName}!Pointer").toUnique("!")

                /**
                 * Variable to hold the raw field value from EVM
                 */
                val rawFieldValue = TACKeyword.TMP(Tag.Bit256, "!field!${fieldName}!Raw").toUnique("!")

                /**
                 * Find the bytemap which holds the field at this offset.
                 */
                val base = lookupBaseFor(PartitionField.StructField(offset)) ?: throw IllegalStateException("Could not find field information for $fieldName")
                /**
                 * Compute the EVM side, add the offset to the pointer [inputSym] wrapped by this object, store the result in fldPointer,
                 * and then read from that index of base and place the result in rawFieldValue
                 */
                val decoding = (CommandWithRequiredDecls(listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = fldPointer,
                        rhs = TACExpr.Vec.Add(
                            offset.asTACExpr,
                            inputSym.asSym()
                        )
                    ),
                    TACCmd.Simple.AssigningCmd.ByteLoad(
                        lhs = rawFieldValue,
                        base = base.partitionVar,
                        loc = fldPointer
                    )
                ), setOf(inputSym, fldPointer, rawFieldValue, base.partitionVar)))
                val recurse = f(fieldIndex, output, base.asRecursiveArg(rawFieldValue))
                return recurse.prependToBlock0(decoding)
            }
        })
    }

    fun expectStaticArrayImpl(
        inputSym: TACSymbol.Var,
        output: CVLDataOutput,
        numElements: BigInteger,
        elementTag: Tag,
        f: (fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        return output.startStaticArray(numElements).foreachElem { it, elemOutput ->
            /**
             * The pointer to the field which holds the value to decode
             */
            val fieldPointer = TACKeyword.TMP(Tag.Bit256, "!field$it").toUnique("!")

            /**
             * The raw field value
             */
            val primitiveField = TACKeyword.TMP(Tag.Bit256, "!field$it!value").toUnique("!")
            val rawOffset = it.toBigInteger() * EVM_WORD_SIZE

            val base = lookupBaseFor(PartitionField.StructField(rawOffset)) ?: error("cannot deref static array without partition information")

            /**
             * Get the partition we are reading from. Note that we can only decode primitives, so this will fail if the "struct field"
             * for the static array is found to not be a [InternalFuncValueLocation.PrimitiveField]
             */
            val targetField = base.partitionVar

            /**
             * Add the relative field offset to this pointer [inputSym], store the result in fieldPointer, and then load
             * from targetField at fieldPointer, placing the result in primitiveField
             */
            val ret = CommandWithRequiredDecls(listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = fieldPointer,
                    rhs = TACExpr.Vec.Add(
                        inputSym.asSym(), rawOffset.asTACExpr
                    )
                ),
                TACCmd.Simple.AssigningCmd.ByteLoad(
                    lhs = primitiveField,
                    base = targetField,
                    loc = fieldPointer
                )
            ), setOf(targetField, fieldPointer, primitiveField, inputSym))
            f(elemOutput, base.asRecursiveArg(primitiveField)).prependToBlock0(ret)
        }
    }

    fun expectArrayImpl(inputSym: TACSymbol.Var, output: CVLDataOutput, eSize: Int, f: (loc: TACSymbol, part: TACSymbol.Var, write: ArrayWriter, gen: (TACSymbol.Var) -> EVMInternalArgData) -> CVLTACProgram): CVLTACProgram {
        /**
         * We must, at least, read the length
         */
        val lengthField = lookupBaseFor(PartitionField.ArrayLength) ?: throw IllegalStateException("Cannot find length field for $inputSym")

        /**
         * Variable to hold the length
         */
        val lengthValue = TACKeyword.TMP(Tag.Bit256, "!DecodedLength").toUnique("!")
        val decode = mutableListOf<CommandWithRequiredDecls<TACCmd.Spec>>()
        /**
         * read the length, and update the length of the array [output] accordingly.
         */
        decode.add(CommandWithRequiredDecls(listOf(
            TACCmd.Simple.AssigningCmd.ByteLoad(
                lhs = lengthValue,
                base = lengthField.partitionVar,
                loc = inputSym
            )
        ), setOf(lengthValue, inputSym, lengthField.partitionVar)))
        val elemField = lookupBaseFor(PartitionField.ArrayElement(eSize))
        // can happen for provably empty arrays, assert the PTA got this right
        val elemStart : TACSymbol
        val length : TACSymbol
        if(elemField == null) {
            val lenCmp = TACKeyword.TMP(Tag.Bool, "!lengthSanity").toUnique("!")
            decode.add(CommandWithRequiredDecls(listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = lenCmp,
                    rhs = TACExpr.BinRel.Eq(
                        lengthValue.asSym(),
                        TACSymbol.Zero.asSym()
                    )
                ),
                TACCmd.Simple.AssertCmd(
                    lenCmp, "Sanity check on empty array length"
                )
            ), setOf(lenCmp, lengthValue)))
            elemStart = TACSymbol.Zero
            length = TACSymbol.Zero
        } else {
            /**
             * Otherwise, compute the data start location, and then initialize [output]'s data by long copying
             * from the elemField partition at that position.
             */
            val fieldStart = TACKeyword.TMP(Tag.Bit256, "!arrayDataField").toUnique("!")
            decode.add(CommandWithRequiredDecls(listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = fieldStart,
                    rhs = TACExpr.Vec.Add(
                        inputSym.asSym(),
                        EVM_WORD_SIZE.asTACExpr
                    )
                ),
            ), setOf(inputSym, fieldStart, lengthValue, elemField.partitionVar)))
            elemStart = fieldStart
            length = lengthValue
        }
        return output.startDynamicArray(length).let { writer ->
            f(elemStart, elemField?.partitionVar ?: TACKeyword.TMP(Tag.ByteMap, "!empty").toUnique("!"), writer) {
                elemField?.asRecursiveArg(it) ?: throw UnsupportedOperationException("Shouldn't be trying to copy to empty array")
            }
        }.prependToBlock0(CommandWithRequiredDecls.mergeMany(decode))
    }
}

private class UnsplitArg(
    val inputSym: TACSymbol.Var,
    val memoryArg: TACSymbol.Var
) : EVMInternalArgData, ReferenceHandlerMixin<TACSymbol.Var>, PrimitiveHandlerMixin {
    override fun expectPrimitive(
        output: CVLDataOutput,
        enc: Tag.CVLArray.UserArray.ElementEncoding,
        clean: (TACSymbol.Var) -> Pair<TACSymbol.Var, CommandWithRequiredDecls<TACCmd.Spec>>
    ): CVLTACProgram {
        return expectPrimitiveImpl(inputSym, output, enc, clean)
    }

    override fun expectStruct(
        output: CVLDataOutput,
        fieldNameToOrdinal: Map<String, Int>,
        f: (ind: Int, fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        return expectStructImpl(inputSym, output, fieldNameToOrdinal, f)
    }

    override fun expectStaticArray(
        output: CVLDataOutput,
        numElements: BigInteger,
        elementTag: Tag,
        f: (fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        return expectStaticArrayImpl(inputSym, output, numElements, elementTag, f)
    }

    override fun expectArray(
        output: CVLDataOutput,
        eSize: Int,
        f: (TACSymbol, TACSymbol.Var, ArrayWriter, (TACSymbol.Var) -> EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        return expectArrayImpl(inputSym, output, eSize, f)
    }

    override fun lookupBaseFor(partitionField: PartitionField): TACSymbol.Var {
        return memoryArg
    }

    override fun TACSymbol.Var.asRecursiveArg(nextField: TACSymbol.Var): EVMInternalArgData {
        return UnsplitArg(
            inputSym = nextField,
            memoryArg = this
        )
    }

    override val TACSymbol.Var.partitionVar: TACSymbol.Var
        get() = this

}

/**
 * The primitive version of [EVMInternalArgData]
 */
private class PrimitiveArg(val inputSym: TACSymbol.Var) : EVMInternalArgData, PrimitiveHandlerMixin {
    override fun expectPrimitive(
        output: CVLDataOutput,
        enc: Tag.CVLArray.UserArray.ElementEncoding,
        clean: (TACSymbol.Var) -> Pair<TACSymbol.Var, CommandWithRequiredDecls<TACCmd.Spec>>
    ): CVLTACProgram {
        return expectPrimitiveImpl(inputSym, output, enc, clean)
    }

    override fun expectStruct(
        output: CVLDataOutput,
        fieldNameToOrdinal: Map<String, Int>,
        f: (ind: Int, fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        throw UnsupportedOperationException("$inputSym is not a reference type argument")
    }

    override fun expectStaticArray(
        output: CVLDataOutput,
        numElements: BigInteger,
        elementTag: Tag,
        f: (fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        throw UnsupportedOperationException("$inputSym is not a reference type argument")
    }

    override fun expectArray(
        output: CVLDataOutput,
        eSize: Int,
        f: (TACSymbol, TACSymbol.Var, ArrayWriter, (TACSymbol.Var) -> EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        throw UnsupportedOperationException("$inputSym is not a reference type argument")
    }
}

private class ReferenceArg(
    val inputSym: TACSymbol.Var,
    val fields: Map<PartitionField, InternalFuncValueLocation.PointerLayoutInfo>
) : EVMInternalArgData, ReferenceHandlerMixin<InternalFuncValueLocation.PointerLayoutInfo> {
    override fun expectPrimitive(
        output: CVLDataOutput,
        enc: Tag.CVLArray.UserArray.ElementEncoding,
        clean: (TACSymbol.Var) -> Pair<TACSymbol.Var, CommandWithRequiredDecls<TACCmd.Spec>>
    ): CVLTACProgram {
        throw UnsupportedOperationException("$inputSym is not a primitive variable")
    }

    override fun expectStruct(
        output: CVLDataOutput,
        fieldNameToOrdinal: Map<String, Int>,
        f: (ind: Int, fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        return expectStructImpl(inputSym, output, fieldNameToOrdinal, f)
    }

    override fun expectStaticArray(
        output: CVLDataOutput,
        numElements: BigInteger,
        elementTag: Tag,
        f: (fieldVar: CVLDataOutput, argData: EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        return expectStaticArrayImpl(inputSym, output, numElements, elementTag, f)
    }

    override fun expectArray(
        output: CVLDataOutput,
        eSize: Int,
        f: (TACSymbol, TACSymbol.Var, ArrayWriter, (TACSymbol.Var) -> EVMInternalArgData) -> CVLTACProgram
    ): CVLTACProgram {
        return expectArrayImpl(inputSym, output, eSize, f)
    }

    override fun lookupBaseFor(partitionField: PartitionField): InternalFuncValueLocation.PointerLayoutInfo? {
        return fields[partitionField]
    }

    override fun InternalFuncValueLocation.PointerLayoutInfo.asRecursiveArg(nextField: TACSymbol.Var): EVMInternalArgData {
        /**
         * What is the rough "type" of the field? A primitive or a reference. It determines the wrapper object
         *  we pass through to the field decoder (and which operation it therefore supports)
         */
        return when (this) {
            is InternalFuncValueLocation.PrimitiveField -> {
                PrimitiveArg(nextField)
            }

            is InternalFuncValueLocation.ReferenceField -> {
                ReferenceArg(
                    inputSym = nextField,
                    fields = this.fields
                )
            }
        }
    }

    override val InternalFuncValueLocation.PointerLayoutInfo.partitionVar: TACSymbol.Var
        get() = this.partitionVariable

}
