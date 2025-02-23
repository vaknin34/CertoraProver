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

package spec.converters.repr

import analysis.CommandWithRequiredDecls
import datastructures.stdcollections.*
import analysis.merge
import evm.EVM_WORD_SIZE
import evm.EVM_WORD_SIZE_INT
import spec.CVLCompiler
import spec.ProgramGenMixin.Companion.andThen
import spec.SafeMathCodeGen
import tac.DataField
import tac.ObjectShape
import tac.Tag
import vc.data.*
import java.math.BigInteger

/**
 * Input for accessing values that are stored in bytemaps. [rootVar] is an array variable inside which
 * this value is stored, and [dataPath] is the path to the specific component of [rootVar] in which
 * this value is stored.(see the documentation of [tac.Tag.CVLArray.UserArray]
 * for an explanation of data layout in CVL). [ptr] is the *physical* index pointing to some location the bytemap
 * identified by the pair [rootVar], [dataPath].
 * In the documentation for this class, we will refer to the value "pointed to" by this; this refers to the value
 * at the index [ptr] in the bytemap identified by [rootVar], [dataPath].
 *
 * [objectShape] is the shape of the value pointed to by this.
 */
class CVLComplexInput(
    val rootVar: TACSymbol.Var,
    val dataPath: List<DataField>,
    override val context: CVLCompiler.CallIdContext,
    val objectShape: ObjectShape,
    val ptr: TACSymbol
) : CVLDataInput, SafeMathCodeGen {
    override fun <R: WithCVLProgram<R>> struct(): StructReader<R> {
        require(objectShape is ObjectShape.Struct)
        /**
         * Then this object points to a struct pointer, that is, the value stored at [ptr] in [rootVar], [dataPath]
         * is itself a pointer. Call this value p. Using the EVM layout, the first field f of this struct is
         * at `p` in [dataPath] + StructField(f), the second field g is at `p + 32` in [dataPath] + Structfield(f2), etc.
         */
        return object : StructReader<R> {
            override fun readField(f: String, cb: (CVLDataInput) -> R): R {
                val ind = objectShape.fields.indexOfFirst {
                    it.first == f
                }.takeIf { it >= 0 } ?: throw IllegalArgumentException("Unknown field $f")
                val fieldOffset = ind * EVM_WORD_SIZE_INT
                val basePointer = TACKeyword.TMP(Tag.Bit256, "!where")
                /**
                 fieldLocation is the pointer for the [CVLComplexInput] object we are passing to [cb].
                 */
                val fieldLocation = TACKeyword.TMP(Tag.Bit256, "!field")
                val prefix = CommandWithRequiredDecls<TACCmd.Spec>(listOf(
                    // read the pointer from the currect location
                    TACCmd.CVL.ReadElement(
                        dataPath = dataPath,
                        lhs = basePointer,
                        useEncoding = Tag.CVLArray.UserArray.ElementEncoding.Unsigned,
                        physicalIndex = ptr,
                        base = rootVar
                    )
                ), setOf(basePointer, ptr, rootVar)).merge(
                    // and then add the field offset, to yield the pointer to the value for field f
                    safeAdd(lhs =  fieldLocation, fieldOffset.asTACSymbol(), basePointer)
                )
                /**
                 * recurse, adding [tac.DataField.StructField] to the current path.
                 */
                return prefix andThen cb(CVLComplexInput(
                    rootVar, dataPath + DataField.StructField(f), context, objectShape.fields[ind].second, fieldLocation
                )) withLabel "Reading struct field $f"
            }

        }
    }

    /**
     * Dual of the [CVLDirectInput.InnerReader]. [elemShape] is the shape of the array elements,
     * [elementSize] is the size of the elements (32 or 1), [len] is the (potentially static) length of the array,
     * and [dataPointer] is the physical location of the start of the data in [dataPath] + [DataField.ArrayData].
     */
    private inner class InnerReader(
        val elemShape: ObjectShape,
        val dataPointer: TACSymbol.Var,
        val len: TACSymbol,
        val elementSize: BigInteger
    ) : ArrayReader {
        override fun foreachElem(f: (Int, CVLDataInput) -> CVLTACProgram): CVLTACProgram {
            return generateUnrolledLoop(emptyProgram(), len) { ind ->
                readElem(ind) { elemReader ->
                    f(ind, elemReader)
                }
            }.appendToSinks(generateUnrollBound(len)).actionLabel("Iterating over elements")
        }

        override fun <R: WithCVLProgram<R>> readElem(i: Int, f: (CVLDataInput) -> R): R {
            return readElemAtOffset((i.toBigInteger() * elementSize).asTACSymbol(), f).actionLabel("Reading element $i")
        }

        override fun <R : WithCVLProgram<R>> readElem(idx: TACSymbol, f: (CVLDataInput) -> R): R {
            val offs = TACKeyword.TMP(Tag.Bit256, "!rel")
            val prefix = safeMul(offs, idx, elementSize.asTACSymbol())
            return prefix andThen readElemAtOffset(offs, f) withLabel "Reading element $idx"
        }

        private fun <R : WithCVLProgram<R>> readElemAtOffset(offset: TACSymbol, f: (CVLDataInput) -> R): R {
            /**
             * add [offset] to [dataPointer] and then generate a new [CVLComplexInput] at this location (indPointer),
             * appending [tac.DataField.ArrayData] onto the enclosing [CVLDirectInput]'s [dataPath], indicating that the
             * value of this element pointer is stored at indPointer in the bytemap identified by [rootVar], [dataPath] + [tac.DataField.ArrayData]
             */
            val indPointer = TACKeyword.TMP(Tag.Bit256, "!elemPointer")
            return safeAdd(indPointer, dataPointer, offset) andThen f(CVLComplexInput(
                rootVar, dataPath + DataField.ArrayData, context, elemShape, indPointer
            ))
        }

        override fun toOutput(f: (TACCmd.CVL.BufferPointer) -> CVLTACProgram): CVLTACProgram {
            return f(
                /**
                 * The buffer pointer is just the offset of the data [dataPointer] at the bytemap identified by [dataPath] + [tac.DataField.ArrayData]
                 */
                TACCmd.CVL.BufferPointer(
                    offset = dataPointer,
                    buffer = TACCmd.CVL.Buffer.CVLBuffer(
                        dataPath = dataPath + DataField.ArrayData,
                        root = rootVar
                    )
                )
            ).actionLabel("Copying data")
        }

    }

    override fun toActionLabel(phrase: String) = "$phrase from $rootVar at path $dataPath"


    override fun <R: WithCVLProgram<R>> staticArray(len: BigInteger, f: (ArrayReader) -> R): R {
        require(objectShape is ObjectShape.StaticArray && objectShape.length == len)
        val arrayPointer = TACKeyword.TMP(Tag.Bit256, "!pointer")
        /**
         * Then the value at [ptr] is a static array pointer, read that value...
         */
        val prefix = CommandWithRequiredDecls(listOf(
            TACCmd.CVL.ReadElement(
                lhs = arrayPointer,
                dataPath = dataPath,
                base = rootVar,
                physicalIndex = ptr,
                useEncoding = Tag.CVLArray.UserArray.ElementEncoding.Unsigned
            )
        ), setOf(rootVar, ptr, arrayPointer))
        /**
         * And pass it directly to [InnerReader] (there is no need to bump by 32 bytes)
         */
        return prefix andThen f(InnerReader(objectShape.elements, arrayPointer, len.asTACSymbol(), EVM_WORD_SIZE)) withLabel "Reading static array"
    }

    override fun <R: WithCVLProgram<R>> dynamicArray(
        callBack: (dynamicLengthVar: TACSymbol.Var, context: CVLCompiler.CallIdContext, reader: ArrayReader) -> R
    ): R {
        require(objectShape is ObjectShape.Array)
        val lenField = TACKeyword.TMP(Tag.Bit256, "!length")
        val arrayPointer = TACKeyword.TMP(Tag.Bit256, "!pointer")
        val dataOffset = TACKeyword.TMP(Tag.Bit256, "!elems")

        val prefix = CommandWithRequiredDecls(listOf(
                /**
                 * Then [ptr] is the location of an array pointer, read the value of that pointer...
                 */
                TACCmd.CVL.ReadElement(
                    lhs = arrayPointer,
                    dataPath = dataPath,
                    base = rootVar,
                    physicalIndex = ptr,
                    useEncoding = Tag.CVLArray.UserArray.ElementEncoding.Unsigned
                ),
                /**
                 * Then read the length of that pointer, from [dataPath] + [tac.DataField.ArrayLength].
                 */
                TACCmd.CVL.ReadElement(
                    lhs = lenField,
                    dataPath = dataPath + DataField.ArrayLength,
                    useEncoding = Tag.CVLArray.UserArray.ElementEncoding.Unsigned,
                    physicalIndex = arrayPointer,
                    base = rootVar,
                )
            ), setOf(arrayPointer, rootVar, lenField, ptr)
        ).merge(
            /**
             * then bump the array pointer by 32 bytes to yield the location of the data.
             */
            safeAdd(dataOffset, EVM_WORD_SIZE.asTACSymbol(), arrayPointer)
        ).toProg("setup")
        val prog = callBack(lenField, context, InnerReader(objectShape.elements, dataOffset, lenField, if(objectShape.isPacked) {
            BigInteger.ONE
        } else {
            EVM_WORD_SIZE
        }))
        return prefix andThen prog withLabel ("Reading dynamic array")
    }

    override fun <R: WithCVLProgram<R>> readPrimitive(
        f: (TACSymbol.Var, CVLCompiler.CallIdContext) -> R
    ): R {
        require(objectShape is ObjectShape.Primitive)
        /**
         * Note that we use [tac.Tag.Bit256] for the primitives that
         * use [tac.Tag.CVLArray.UserArray.ElementEncoding.Unsigned]. This is because we could be reading either bytesK or
         * a uint type, the former of which can't be [Tag.Int]. However, using a [Tag.Bit256] for a Uintk type is fine,
         * because that can be used interchangeably with a [Tag.Int] (as the value is unsigned).
         */
        val resultTag = when(objectShape.enc) {
            Tag.CVLArray.UserArray.ElementEncoding.Signed -> Tag.Int
            Tag.CVLArray.UserArray.ElementEncoding.Unsigned -> Tag.Bit256
            Tag.CVLArray.UserArray.ElementEncoding.Boolean -> Tag.Bool
        }
        val tmp = TACKeyword.TMP(resultTag, "!elem")
        val doRead = CommandWithRequiredDecls(
            listOf(
                TACCmd.CVL.ReadElement(
                    lhs = tmp,
                    useEncoding = objectShape.enc,
                    physicalIndex = ptr,
                    dataPath = dataPath,
                    base = rootVar
                )
            ), setOf(ptr, tmp, rootVar)
        )
        return doRead andThen f(tmp, context) withLabel "Moving primitive"
    }
}
