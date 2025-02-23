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

import datastructures.stdcollections.*
import analysis.CommandWithRequiredDecls
import analysis.merge
import evm.EVM_WORD_SIZE
import evm.EVM_WORD_SIZE_INT
import spec.CVLCompiler
import spec.ProgramGenMixin
import spec.ProgramGenMixin.Companion.andThen
import spec.ProgramGenMixin.Companion.then
import spec.toProg
import tac.DataField
import tac.ObjectShape
import tac.Tag
import utils.mapSecond
import utils.mapToSet
import vc.data.*
import java.math.BigInteger

/**
 * Like [CVLDirectInput], this class is when the output is stored "directly" in a variable.
 */
class CVLDirectOutput(val tgt: TACSymbol.Var, override val context: CVLCompiler.CallIdContext) : CVLDataOutput, ProgramGenMixin {
    override fun startStruct(structWriter: StructWriter): CVLTACProgram {
        check(tgt.tag is Tag.UserDefined.Struct)
        val (flds, setup) = (tgt.tag as Tag.UserDefined.Struct).fields.mapIndexed { ind, fld ->
            /**
             * For each field of this struct, generate a temp variable to hold the value of the field,
             * invoke the struct writer's [spec.converters.repr.StructWriter.generateField] with
             * a [spec.converters.repr.CVLDirectOutput] wrapping this temp variable, and then package this up.
             */
            val tmpOutput = TACKeyword.TMP(fld.type, "!field${fld.name}")
            (fld.name to tmpOutput) to structWriter.generateField(CVLDirectOutput(tmpOutput, context), fld.name, ind).actionLabel("Write field ${fld.name}")
        }.unzip().mapSecond { progs ->
            progs.reduce(::mergeCodes)
        }
        /**
         * setup now contains all of the code that places the values of the fields into the variables
         * identified by flds. Then create a [vc.data.TACExpr.StructConstant] from flds, and place that
         * into tgt.
         */
        return setup then
            CommandWithRequiredDecls(listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = tgt,
                    rhs = TACExpr.StructConstant(flds.associate { (fld, v) ->
                        fld to v.asSym()
                    }, tag = tgt.tag)
                )
            ), setOf(tgt) + flds.mapToSet { it.second }).toProg("encode") withLabel ("Write struct")
    }

    /**
     * Create an [ArrayWriter] for this variable, whose length is [len], element types are given by [elementType],
     * and whose element size is given by [eSz]. [explicitlySetLength] determines whether the length of the array is
     * written (using [TACCmd.CVL.SetArrayLength])
     */
    private fun makeWriter(
        len: TACSymbol,
        explicitlySetLength: Boolean,
        eSz: BigInteger,
        elementType: ObjectShape
    ) : ArrayWriter {
        fun writeLengthCmd() = if(explicitlySetLength) {
            TACCmd.CVL.SetArrayLength(
                lhs = tgt,
                len = len
            )
        } else {
            null
        }
        return object : ArrayWriter {
            override fun longCopy(pointer: TACCmd.CVL.BufferPointer): CVLTACProgram {
                return CommandWithRequiredDecls(listOfNotNull(
                    /**
                     * Simply array copy from [pointer] into the data of [tgt].
                     */
                    TACCmd.CVL.ArrayCopy(
                        dst = TACCmd.CVL.BufferPointer(
                            offset = TACSymbol.Zero,
                            buffer = TACCmd.CVL.Buffer.CVLBuffer(
                                root = tgt,
                                dataPath = listOf(DataField.ArrayData)
                            )
                        ),
                        src = pointer,
                        logicalLength = len,
                        elementSize = eSz.intValueExact()
                    ),
                    /**
                     * And write the length if needed
                     */
                    writeLengthCmd()
                ), pointer.getReferencedSyms() + tgt + len).toProg("array copy").actionLabel("Direct copy array elements")
            }

            override fun foreachElem(f: (Int, CVLDataOutput) -> CVLTACProgram): CVLTACProgram {
                /**
                 * Otherwise, create an unroll bound, and set the array length...
                 */
                val suffixCode = generateUnrollBound(len).merge(CommandWithRequiredDecls(listOfNotNull(
                    writeLengthCmd()
                ), setOf(len, tgt))).toProg("setup code", context)
                /**
                 * And then use that as the "suffix" of the unrolled loop, each iteration of which is generated by
                 * passing [CVLComplexOutput] to [f] (this is where the switch from direct to complex occurs).
                 */
                return generateUnrolledLoop(suffixCode, len) { ind ->
                    val output = TACKeyword.TMP(Tag.Bit256, "!elem")
                    val readElement = CommandWithRequiredDecls(
                        listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = output,
                                rhs = (ind * EVM_WORD_SIZE_INT).asTACExpr
                            )
                        ), setOf(output)
                    )
                    readElement andThen
                    f(ind, CVLComplexOutput(
                        ptr = output,
                        context = context,
                        rootVar = tgt,
                        currPath = listOf(DataField.ArrayData),
                        objectShape = elementType
                    )) withLabel "Iteration $ind"
                }.actionLabel("Iterate over array")
            }
        }

    }

    override fun startStaticArray(len: BigInteger): ArrayWriter {
        val tg = tgt.tag
        check(tg is Tag.CVLArray.UserArray && !tg.isPacked) {
            "Invalid tag for static array output at $tgt"
        }
        return makeWriter(
            len = len.asTACSymbol(),
            elementType = tg.elementType,
            eSz = EVM_WORD_SIZE,
            explicitlySetLength = false
        )
    }

    override fun startDynamicArray(len: TACSymbol): ArrayWriter {
        val tg = tgt.tag as? Tag.CVLArray ?: throw IllegalStateException("Trying to treat $tgt as a dynamic array, it's tag is ${tgt.tag}")
        when(tg) {
            Tag.CVLArray.RawArray -> {
                /**
                 * For raw arrays, we only support long copies
                 *
                 * note: I don't actually know what rawarray values we allow writing to, but okay.
                 */
                return object : ArrayWriter {
                    override fun longCopy(pointer: TACCmd.CVL.BufferPointer): CVLTACProgram {
                        return CommandWithRequiredDecls(
                            listOf(
                                TACCmd.CVL.ArrayCopy(
                                    dst = TACCmd.CVL.BufferPointer(
                                        offset = TACSymbol.Zero,
                                        buffer = TACCmd.CVL.Buffer.CVLBuffer(tgt, listOf(DataField.ArrayData))
                                    ),
                                    src = pointer,
                                    logicalLength = len,
                                    elementSize = 1
                                ),
                                TACCmd.CVL.SetArrayLength(
                                    lhs = tgt,
                                    len = len
                                )
                            ), pointer.getReferencedSyms() + tgt
                        ).toProg("array copy").actionLabel("Copy elements")
                    }

                    override fun foreachElem(f: (Int, CVLDataOutput) -> CVLTACProgram): CVLTACProgram {
                        throw UnsupportedOperationException("cannot iterate on small arrays")
                    }
                }
            }
            is Tag.CVLArray.UserArray -> {
                return makeWriter(
                    len,
                    explicitlySetLength = true,
                    elementType = tg.elementType,
                    eSz = if(tg.isPacked) {
                        BigInteger.ONE
                    } else {
                        EVM_WORD_SIZE
                    }
                )
            }
        }
    }

    /**
     * Like the case in [CVLDirectInput], the variable [tgt] already holds the value, so just have the callback
     * [f] assign to it directly.
     */
    override fun movePrimitive(f: (TACSymbol.Var, CVLCompiler.CallIdContext) -> CVLTACProgram): CVLTACProgram {
        return f(this.tgt, context).actionLabel("Move primitive value")
    }

    override fun toActionLabel(phrase: String): String {
        return "$phrase for variable $tgt"
    }
}
