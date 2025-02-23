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
import evm.EVM_WORD_SIZE
import spec.CVLCompiler
import spec.ProgramGenMixin.Companion.andThen
import spec.ProgramGenMixin.Companion.label
import spec.SafeMathCodeGen
import tac.DataField
import tac.ObjectShape
import tac.Tag
import vc.data.*
import java.math.BigInteger

/**
 * The case when the data being read from is a variable [s]; i.e., we are reading directly from
 * variables.
 */
class CVLDirectInput(val s: TACSymbol.Var, override val context: CVLCompiler.CallIdContext) : CVLDataInput {
    override fun <R: WithCVLProgram<R>> struct(): StructReader<R> {
        val vTag = s.tag
        require(vTag is Tag.UserDefined.Struct)
        return object : StructReader<R> {
            /**
             * This struct reader simply projects out the requested field into a temporary variable
             * and calls [cb] with a new [CVLDirectInput] wrapping that variable.
             */
            override fun readField(f: String, cb: (CVLDataInput) -> R): R {
                val fld = vTag.fields.find {
                    it.name == f
                } ?: throw IllegalArgumentException("Unknown field $f for struct $vTag")
                val tmp = TACKeyword.TMP(fld.type, "!field${fld.name}")
                val structRead = CommandWithRequiredDecls(
                    listOf(
                        /**
                         * Read the struct field, and prepend that to the code returned by [cb]
                         */
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            lhs = tmp,
                            rhs = TACExpr.StructAccess(
                                struct = s.asSym(),
                                tag = fld.type,
                                fieldName = f
                            )
                        )
                    ), setOf(s, tmp)
                )
                return structRead andThen cb(CVLDirectInput(tmp, context)) withLabel ("Read struct field $f")
            }
        }
    }

    /**
     * Common class for the static array and dynamic array cases. [elemShape] is the shape of the elements, [len] is the
     * (potentially) static length of the array, and [elemSize] is the element size (1 or 32)
     *
     */
    private inner class InnerReader(val elemShape: ObjectShape, val len: TACSymbol, val elemSize: BigInteger) : ArrayReader, SafeMathCodeGen {
        override fun foreachElem(f: (Int, CVLDataInput) -> CVLTACProgram): CVLTACProgram {
            return generateUnrolledLoop(emptyProgram(), len) {
                readElem(it) { input ->
                    f(it, input)
                }
            }.appendToSinks(generateUnrollBound(len)).actionLabel("Unroll loop")
        }

        /**
         * This is a separate implementation because we can generate a constant offset, instead of generating
         * safe mul code. This is where the "switch" from direct to complex inputs happens.
         */
        override fun <R: WithCVLProgram<R>> readElem(i: Int, f: (CVLDataInput) -> R): R {
            val dataInput = CVLComplexInput(
                objectShape = elemShape,
                dataPath = listOf(DataField.ArrayData),
                rootVar = s,
                context = context,
                ptr = (i.toBigInteger() * elemSize).asTACSymbol()
            )
            return f(dataInput).actionLabel("Read element at $i")
        }

        /**
         * Compute the physical index by (safe) multiplying [idx] by the element size, and then
         * pass in the new [CVLComplexInput] to [f].
         */
        override fun <R : WithCVLProgram<R>> readElem(idx: TACSymbol, f: (CVLDataInput) -> R): R {
            val offs = TACKeyword.TMP(Tag.Bit256, "!physicalIdx")
            val prefix = safeMul(offs, idx, elemSize.asTACSymbol())
            return prefix andThen f(CVLComplexInput(
                objectShape = elemShape,
                dataPath = listOf(DataField.ArrayData),
                rootVar = s,
                context = context,
                ptr = offs
            )) withLabel "Read element at $idx"
        }

        override fun toOutput(f: (TACCmd.CVL.BufferPointer) -> CVLTACProgram): CVLTACProgram {
            return f(
                TACCmd.CVL.BufferPointer(
                    offset = TACSymbol.Zero,
                    buffer = TACCmd.CVL.Buffer.CVLBuffer(
                        s, listOf(DataField.ArrayData)
                    )
                )
            ).actionLabel("Long copy array")
        }

    }

    override fun <R: WithCVLProgram<R>> staticArray(len: BigInteger, f: (ArrayReader) -> R): R {
         val tag = s.tag as? Tag.CVLArray.UserArray ?: throw IllegalStateException("Trying to treat variable $s with tag ${s.tag} as an array; it isn't")
        /**
         * Just generate the [InnerReader] and call [f], nothing extra to add
         */
        return f(InnerReader(tag.elementType, len.asTACSymbol(), EVM_WORD_SIZE)).actionLabel("Read static array")
    }

    override fun <R : WithCVLProgram<R>> dynamicArray(
        callBack: (dynamicLengthVar: TACSymbol.Var, context: CVLCompiler.CallIdContext, reader: ArrayReader) -> R
    ): R {
        val t = (s.tag as? Tag.CVLArray.UserArray) ?: throw IllegalStateException("Trying to treat variable $s with tag ${s.tag} as dynamic array, it isn't")
        val len = TACKeyword.TMP(Tag.Bit256, "!len")
        /**
         * Read the length of the array into len, use that to construct [InnerReader], and also
         * pass that along to [callBack]. Prepend to this the code that actually reads out the length of the array.
         */
        return CommandWithRequiredDecls(listOf(
            TACCmd.CVL.ArrayLengthRead(
                lhs = len,
                rhs = s
            )
        ), setOf(len, s)).label("Read array length") andThen callBack(len, context, InnerReader(t.elementType, len, if(t.isPacked) {
            BigInteger.ONE
        } else {
            EVM_WORD_SIZE
        })) withLabel "Read dynamic array"
    }

    /**
     * in this case, the variable is just [s], so pass that directly to [f].
     */
    override fun <R: WithCVLProgram<R>> readPrimitive(
        f: (TACSymbol.Var, CVLCompiler.CallIdContext) -> R
    ): R {
        return f(this.s, context).actionLabel("Read primitive")
    }

    override fun toActionLabel(phrase: String): String {
        return "$phrase from $s"
    }
}
