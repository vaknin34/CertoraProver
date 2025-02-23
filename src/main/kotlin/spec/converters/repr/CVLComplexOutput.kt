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
import evm.alignToEVMWord
import spec.CVLCompiler
import spec.CodeGenUtils
import spec.ProgramGenMixin.Companion.andThen
import spec.ProgramGenMixin.Companion.then
import spec.SafeMathCodeGen
import spec.toProg
import tac.DataField
import tac.ObjectShape
import tac.Tag
import utils.`impossible!`
import vc.data.*
import java.math.BigInteger

/**
 * Output analogue of [CVLComplexInput]. As there, [rootVar] and [currPath] together identify a bytemap which
 * holds the value being encapsulated by this class. [ptr] is the location within that buffer which holds the value
 * "pointed to" by this class. [objectShape] is the shape of the value stored at that location.
 *
 * Because this class destructively writes into bytemaps, we need to make sure that multiple initializations do not overlap
 * with one another. We accomplish this with a "free" pointer which is attached to [rootVar] and accessed using
 * the [vc.data.TACCmd.CVL.LocalAlloc] command. This effectively gives us a way to thread through state (the next available pointer)
 * during a signle output operation without the messiness that we have with the encoder (where we thread through the next
 * pointer everywhere).
 */
class CVLComplexOutput(
    private val rootVar: TACSymbol.Var,
    private val currPath: List<DataField>,
    private val objectShape: ObjectShape,
    private val ptr: TACSymbol.Var,
    override val context: CVLCompiler.CallIdContext
) : CVLDataOutput, SafeMathCodeGen {
    override fun toActionLabel(phrase: String) = "$phrase at $ptr for $rootVar with path $currPath"

    /**
     * Allocates an initializes a struct pointer, which is then written into the location in this buffer.
     */
    override fun startStruct(structWriter: StructWriter): CVLTACProgram {
        check(objectShape is ObjectShape.Struct)
        /**
         * Compute the size of the buffer.
         */
        val sz = objectShape.fields.size.toBigInteger() * EVM_WORD_SIZE
        val output = TACKeyword.TMP(Tag.Bit256, "!data")

        /**
         * "Allocate" the struct, putting the pointer into output.
         */
        val allocPrefix = CommandWithRequiredDecls(listOf(
            TACCmd.CVL.LocalAlloc(
                amount = sz.asTACSymbol(),
                lhs = output,
                arr = rootVar
            )
        ), setOf(rootVar, output)).toProg("alloc", context).actionLabel("Allocating struct of size $sz")
        /**
         * Then for each field of this struct
         */
        return objectShape.fields.withIndex().fold(allocPrefix) { acc: CVLTACProgram, (ind, fld) ->
            val (fldName, shape) = fld
            /**
             * Holds the pointer for the struct field
             */
            val outputPtr = TACKeyword.TMP(Tag.Bit256, "!field$fldName")

            /**
             * New output at the pointer output pointer, with the current path extended with the appropriate
             * [tac.DataField.StructField].
             */
            val fieldOutput = CVLComplexOutput(
                rootVar, currPath + DataField.StructField(fldName), shape, outputPtr, context
            )

            /**
             * Generate the field, by writing into fieldOutput.
             */
            val prog = structWriter.generateField(fieldOutput, fldName, ind)

            /**
             * Actually compute the pointer offset, and prepend that to the field generation, then APPEND all of that
             * onto the current accumulator.
             */
            val fieldAddition = safeAdd(outputPtr, output, (ind.toBigInteger() * EVM_WORD_SIZE).asTACSymbol())
            acc then (fieldAddition andThen prog withLabel "Writing field $fldName")
        }.appendToSinks(
            /**
             * Finally, append the code that writes the (newly initialized) pointer into
             * the location pointed to by this object.
             */
            CommandWithRequiredDecls(listOf(
                TACCmd.CVL.WriteElement(
                    outputPath = currPath,
                    physicalIndex = ptr,
                    useEncoding = Tag.CVLArray.UserArray.ElementEncoding.Unsigned,
                    value = output,
                    target = rootVar
                ),
            ), setOf(ptr, rootVar, output)).actionLabel("Writing struct pointer $output into $ptr")
        ).actionLabel("Writing struct")
    }

    override fun startStaticArray(len: BigInteger): ArrayWriter {
        return startArray(len.asTACSymbol(), isStatic = true)
    }

    override fun startDynamicArray(len: TACSymbol): ArrayWriter {
        return startArray(len, isStatic = false)
    }

    /**
     * Common code for allocating an array block of length [len],
     * and then generating the code that creates the [ArrayWriter].
     */
    private fun startArray(len: TACSymbol, isStatic: Boolean): ArrayWriter {
        /**
         * Compute the element size, and do some basic "shape" validation
         */
        val eSz = when(objectShape) {
            is ObjectShape.StaticArray -> {
                check(len is TACSymbol.Const && len.value == objectShape.length && isStatic) {
                    "Incorrect object shape $this"
                }
                EVM_WORD_SIZE
            }
            is ObjectShape.Array -> {
                check(!isStatic) {
                    "Not a static array $this"
                }
                if(objectShape.isPacked) {
                    BigInteger.ONE
                } else {
                    EVM_WORD_SIZE
                }
            }
            else -> throw UnsupportedOperationException("Object $objectShape does appear to be an array")
        }
        /**
         * compute the size of the data segment, placing the symbol holding this
         * into allocAmount, and the code used to compute this (if any) into code.
         */
        val (allocAmount, code) = when(len) {
            is TACSymbol.Const -> {
                val totalSize = eSz * len.value
                val sizeAdjusted = totalSize.alignToEVMWord().asTACSymbol()
                sizeAdjusted to null
            }
            is TACSymbol.Var -> {
                val sz = TACKeyword.TMP(Tag.Bit256, "!dataSize")

                /**
                 * (Safe) multiply the amount, placing it into sz
                 */
                val mulCode = safeMul(sz, len, eSz.asTACSymbol())
                if(eSz.mod(EVM_WORD_SIZE) != BigInteger.ZERO) {
                    /**
                     * word align sz if we have non-word aligned element size, and combine that
                     * code with mulCode.
                     */
                    CodeGenUtils.wordAlignSymbol(sz).let { (allocSize, gen) ->
                        allocSize to mulCode.merge(gen)
                    }
                } else {
                    /**
                     * otherwise, return sz and mulCode by themselves
                     */
                    sz to mulCode
                }
            }
        }
        /**
         * allocPointer holds the result of the allocation
         */
        val allocPointer = TACKeyword.TMP(Tag.Bit256, "!alloc")

        /**
         * outputPointer holds the location of the data for the array. For static arrays, this
         * is just allocPointer, otherwise in the dynamic case we bump allocPointer by 32 bytes.
         */
        val outputPointer = TACKeyword.TMP(Tag.Bit256, "!output")
        /**
         * Compute the total allocation size placing into allocSize, and any code required for computing allocSize into
         * adjust. Finally, include the code that computes outputPointer from allocPointer into output.
         */
        val (allocSize, adjust, output) = if(!isStatic) {
            val totalSize = TACKeyword.TMP(Tag.Bit256, "!total")
            Triple(totalSize, safeAdd(totalSize, allocAmount, EVM_WORD_SIZE.asTACSymbol()), safeAdd(outputPointer, allocPointer, EVM_WORD_SIZE.asTACSymbol()))
        } else {
            Triple(allocAmount, null, CommandWithRequiredDecls(listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = outputPointer,
                    rhs = allocPointer.asSym()
                )
            ), setOf(outputPointer, allocPointer)))
        }
        /**
         * Join all of the above together
         *  * code (if non-null) includes the code to compute the size of the elements
         *  * adjust (if non-null) includes the code to compute the total size of the allocated block
         *  * output computes outputPointer from allocPointer
         */
        val allocationCommands = listOfNotNull(
            // (if non-null) includes the code to compute the size of the elements
            code,
            // (if non-null) includes the code to compute the total size of the allocated block
            adjust,
            // Actually allocate allocSize and place the result in allocPointer
            CommandWithRequiredDecls(listOf(
                TACCmd.CVL.LocalAlloc(
                    lhs = allocPointer,
                    arr = rootVar,
                    amount = allocSize
                )
            ), setOfNotNull(allocAmount as? TACSymbol.Var, rootVar, allocPointer)),
            // compute outputSize from allocSize
            output,
            if(!isStatic) {
                // if requested, write len into the location at allocPointer
                CommandWithRequiredDecls(listOf(
                    TACCmd.CVL.WriteElement(
                        value = len,
                        target = rootVar,
                        physicalIndex = allocPointer,
                        useEncoding = Tag.CVLArray.UserArray.ElementEncoding.Unsigned,
                        outputPath = currPath + DataField.ArrayLength
                    )
                ), setOf(allocPointer, len, rootVar)).actionLabel("Writing length of array")
            } else {
                null
            }
        ).let(CommandWithRequiredDecls.Companion::mergeMany).toProg("alloc", context).actionLabel("Allocing array with size $len")
        /*
          Appended to all other code, actually write the pointer we allocated into the location pointed to by this.
         */
        val outputProg = CommandWithRequiredDecls(
            listOf(
                TACCmd.CVL.WriteElement(
                    physicalIndex = ptr,
                    outputPath = currPath,
                    useEncoding = Tag.CVLArray.UserArray.ElementEncoding.Unsigned,
                    target = rootVar,
                    value = allocPointer
                ),
            ), setOf(ptr, rootVar, allocPointer)
        ).toProg("suffix", context).actionLabel("Writing allocated array pointer")

        fun CVLTACProgram.andLabel() = this.actionLabel("Handling array with size $len")

        return object : ArrayWriter {
            override fun longCopy(pointer: TACCmd.CVL.BufferPointer): CVLTACProgram {
                return longCopy(
                    pointer,
                    pointer.getReferencedSyms()
                )
            }

            private fun longCopy(
                bufferSrc: TACCmd.CVL.BufferPointer,
                syms: Set<TACSymbol>
            ): CVLTACProgram {
                return CommandWithRequiredDecls(
                    listOf(
                        TACCmd.CVL.ArrayCopy(
                            dst = TACCmd.CVL.BufferPointer(
                                offset = outputPointer,
                                buffer = TACCmd.CVL.Buffer.CVLBuffer(
                                    root = rootVar,
                                    dataPath = currPath + DataField.ArrayData
                                )
                            ),
                            src = bufferSrc,
                            elementSize = eSz.intValueExact(),
                            logicalLength = len
                        )
                    ), setOf(outputPointer, rootVar) + syms
                ).toProg("copy", env = context).actionLabel("Copying array from $bufferSrc").let { longCopyProg ->
                    /**
                     * Squish the program which long copies between the allocation commands and the program that outputs the pointer.
                     */
                    allocationCommands then longCopyProg then outputProg
                }.andLabel()
            }

            override fun foreachElem(f: (Int, CVLDataOutput) -> CVLTACProgram): CVLTACProgram {
                /**
                 * Otherwise, unroll the loop, using outputProg + an unrolling bound as the suffix for the unrolling
                 */
                return generateUnrolledLoop(outputProg.appendToSinks(generateUnrollBound(len)), len) { ind ->

                    val elemPointer = TACKeyword.TMP(Tag.Bit256, "!offset")

                    /**
                     * Compute the offset of the element, starting from outputPointer.
                     */
                    val computeElemPointer = safeAdd(elemPointer, outputPointer, (ind.toBigInteger() * eSz).asTACSymbol())

                    /**
                     * New output for the element at [ind], extend the current path with [tac.DataField.ArrayData],
                     * and use the newly computed elemPointer.
                     */
                    val dataOutput = CVLComplexOutput(
                        rootVar = rootVar,
                        currPath = currPath + DataField.ArrayData,
                        context = context,
                        objectShape = when(objectShape) {
                            is ObjectShape.Array -> objectShape.elements
                            is ObjectShape.StaticArray -> objectShape.elements
                            is ObjectShape.Primitive,
                            is ObjectShape.Struct -> `impossible!`
                        },
                        ptr = elemPointer
                    )
                    computeElemPointer andThen f(ind, dataOutput) withLabel ("writing elem $ind...")
                }.let { unrolledLoop ->
                    allocationCommands then unrolledLoop
                }.andLabel()
            }
        }
    }

    override fun movePrimitive(f: (TACSymbol.Var, CVLCompiler.CallIdContext) -> CVLTACProgram): CVLTACProgram {
        check(objectShape is ObjectShape.Primitive)
        /**
         * Generate a temporary variable which should hold the value to write. Use [Tag.Int] for
         * the signed and unsigned. Note that this is "opposite" of what we did in the input version;
         * if we are writing an, e.g., bytes3, that will be tagged with [Tag.Bit256], which can be
         * stored without issue into a temp variable with tag [Tag.Int].
         */
        val tmpTag = when(objectShape.enc) {
            Tag.CVLArray.UserArray.ElementEncoding.Signed,
            Tag.CVLArray.UserArray.ElementEncoding.Unsigned -> Tag.Int
            Tag.CVLArray.UserArray.ElementEncoding.Boolean -> Tag.Bool
        }
        val tmp = TACKeyword.TMP(tmpTag, "!toWrite")

        /**
         * Place the result in tmp.
         */
        val decode = f(tmp, context)

        /**
         * Then write tmp into the buffer at the given location, using the specified encoding.
         */
        val suffix = CommandWithRequiredDecls<TACCmd.Spec>(listOf(
                TACCmd.CVL.WriteElement(
                    target = rootVar,
                    value = tmp,
                    useEncoding = objectShape.enc,
                    physicalIndex = ptr,
                    outputPath = currPath
                ),
            ),
            setOfNotNull(rootVar, ptr, tmp)
        ).toProg("move prim", context)
        return decode then suffix withLabel "Encode primitive"
    }

}
