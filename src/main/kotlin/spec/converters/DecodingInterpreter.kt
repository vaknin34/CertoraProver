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
import datastructures.stdcollections.*
import evm.EVM_WORD_SIZE
import spec.converters.DataLayoutInterpreter.Companion.sizeAsEncodedMember
import spec.converters.repr.CVLDataOutput
import spec.converters.repr.StructWriter
import spec.cvlast.abi.DataLayout
import spec.cvlast.typedescriptors.*
import spec.toProg
import tac.Tag
import vc.data.*

/**
 * Object that traverses an ABI encoded buffer (represented by a [LowLevelDecoder] object)
 * according to a [DataLayout].
 */
object DecodingInterpreter : DataLayoutInterpreter {
    /**
     * Decodes a value whose low-level data layout is described by [layout] from the buffer wrapped by the
     * decoder object [l], placing the result in [target].
     *
     * the [onDecode] callback is invoked when data is read out of the buffer, passing in the raw offset
     * within the buffer and the amount being read. This callback may return null, otherwise the results are concatenated
     * with the rest of the decoding code (exactly where is not specified). Typically used to enforce a read does not go outside
     * the bounds of the buffer.
     */
    fun decode(
        target: CVLDataOutput,
        layout: DecoderLayout,
        l: LowLevelDecoder,
        onDecode: ((offsetWithinBuffer: TACSymbol.Var, size: TACSymbol) -> CommandWithRequiredDecls<TACCmd.Spec>?)? = null
    ) : LowLevelDecode {
        return decodeInternal(target, layout, l, onDecode, null)
    }

    /**
     * As [decode] above, but passes along the [sequenceCallback], which is expected to be called
     * when the [spec.cvlast.abi.DataLayout.SequenceOf] constructor is hit. If [sequenceCallback] is null
     * when [spec.cvlast.abi.DataLayout.SequenceOf] is hit, then this function throws.
     */
    private fun decodeInternal(
        target: CVLDataOutput,
        layout: DecoderLayout,
        l: LowLevelDecoder,
        onDecode: ((offsetWithinBuffer: TACSymbol.Var, size: TACSymbol) -> CommandWithRequiredDecls<TACCmd.Spec>?)?,
        sequenceCallback: ((DataLayout.SequenceElement<DecoderLayout>, CVLDataOutput, LowLevelDecoder) -> CVLTACProgram)?
    ) : LowLevelDecode {
        return when(layout) {
            is DataLayout.DynamicPointer -> {
                /*
                 follow the current pointer, resolving w.r.t. the saved scope, and recurse
                 */
                l.deref {
                    decodeInternal(target, layout.next, it, onDecode, sequenceCallback)
                }
            }
            is DataLayout.OpenScope -> {
                /*
                  Save the current scope and recurse
                 */
                l.saveScope { withScope ->
                    decodeInternal(target, layout.next, withScope, onDecode, sequenceCallback)
                }
            }
            is DataLayout.Terminal -> {
                when(val t = layout.t) {
                    is TerminalAction.ValueType -> {
                        /*
                          For direct values, we just decode a single word
                         */
                        l.terminalAction { buffer, offset, scalar ->
                            target.movePrimitive { tgt, _ ->
                                if(scalar != null) {
                                    /*
                                     If we have a scalar, just use that (this is crucial for decoding return data out
                                     of memory), we must use tacM0x0
                                     */
                                   EVMMoveSemantics.ValueConverters.convertValueTypeToEncoding(
                                        dest = tgt,
                                        destEncoding = t.ty.bufferEncoding,
                                        src = scalar
                                    ).toProg("scalar move", target.context)
                                } else {
                                    /*
                                     Otherwise, read the value out of the buffer, and convert according to the buffer encoding
                                     */
                                    val readValue = TACKeyword.TMP(Tag.Bit256, "!rawFieldValue").toUnique("!")
                                    CommandWithRequiredDecls.mergeMany(listOfNotNull(
                                        onDecode?.invoke(offset, EVM_WORD_SIZE.asTACSymbol()),
                                        CommandWithRequiredDecls(listOf(
                                            TACCmd.Simple.AssigningCmd.ByteLoad(
                                                base = buffer,
                                                loc = offset,
                                                lhs = readValue
                                            )
                                        ), setOf(buffer, offset, readValue)),
                                        EVMMoveSemantics.ValueConverters.convertValueTypeToEncoding(
                                            dest = tgt,
                                            destEncoding = t.ty.expectedBufferEncoding,
                                            src = readValue
                                        )
                                    )).toProg("read", target.context)
                                }
                            }
                        }
                    }
                    is TerminalAction.Composed -> {
                        /**
                         * "opens" the existential type, as in the [EncodingInterpreter]
                         */
                        fun <O, SRC: Any, DST: Any, I> TerminalAction.Composed<O, SRC, DST, I>.unwrap() : ITypeDescriptorConverter<O, SRC, DST>
                           where I : ITypeDescriptorConverter<O, SRC, DST>, I : SupportsSizeQuery = this.conv
                        t.unwrap().convertTo(
                            fromVar = l,
                            toVar = target,
                            cb = { it }
                        ) as CVLTACProgram
                    }
                }
            }
            is DataLayout.TupleOf -> {
                return target.startStruct(object : StructWriter {
                    override fun generateField(output: CVLDataOutput, fieldName: String, fieldIndex: Int): CVLTACProgram {
                        val f = layout.elements[fieldIndex]
                        check(f.first == fieldName)
                        return l.advanceCurr(layout.offsetOfField(fieldIndex)) { fieldDec ->
                            decodeInternal(
                                target = output,
                                l = fieldDec,
                                layout = f.second,
                                onDecode = onDecode,
                                sequenceCallback = sequenceCallback
                            )
                        }
                    }
                })
            }

            is DataLayout.LengthTaggedTuple -> {
                if(sequenceCallback != null) {
                    throw UnsupportedOperationException("Already have staged call back")
                }
                /**
                 * Read the length of the array...
                 */
                l.terminalAction { buffer, offset, scalar ->
                    val len = TACKeyword.TMP(Tag.Bit256, "!length").toUnique("!")
                    val readLength = if(scalar != null) {
                        CommandWithRequiredDecls(listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = len,
                                rhs = scalar
                            )
                        ), setOfNotNull(len, scalar))
                    } else {
                        CommandWithRequiredDecls(listOf(
                            TACCmd.Simple.AssigningCmd.ByteLoad(
                                lhs = len,
                                loc = offset,
                                base = buffer
                            )
                        ), setOf(len, offset, buffer))
                    }
                    /**
                     * Then, advance to where the elements are stored
                     */
                    l.advanceCurr(EVM_WORD_SIZE) { nxt ->
                        /**
                         * And then recurse, saving the following continuation to run when we find
                         * a [spec.cvlast.abi.DataLayout.SequenceOf]
                         */
                        decodeInternal(
                            target, layout.elems, nxt, onDecode
                        ) { seq, tgt, source ->
                            val writer = tgt.startDynamicArray(len = len)
                            when(seq) {
                                is DataLayout.SequenceElement.Elements -> {
                                    /**
                                     * If the elements are value typed, long copy
                                     */
                                    if(seq.dataLayout is DataLayout.Terminal && (seq.dataLayout as DataLayout.Terminal<DecoderTerminal>).t is TerminalAction.ValueType) {
                                        source.terminalAction { elemSource, elemStart, _ ->
                                            writer.longCopy(elemSource, elemStart)
                                        }
                                    } else {
                                        /**
                                         * Otherwise, iterate using the [writer] foreach method,
                                         * populating each element recursively with [decodeInternal]
                                         */
                                        val encodedSize = seq.dataLayout.sizeAsEncodedMember()
                                        writer.foreachElem { ind, elemOutput ->
                                            val encodedOffset = encodedSize * ind.toBigInteger()
                                            source.advanceCurr(encodedOffset) { elemReader ->
                                                decodeInternal(
                                                    elemOutput,
                                                    sequenceCallback = null,
                                                    onDecode = onDecode,
                                                    layout = seq.dataLayout,
                                                    l = elemReader
                                                )
                                            }
                                        }
                                    }
                                }
                                is DataLayout.SequenceElement.PackedBytes1 -> {
                                    /**
                                     * We always long copy packed arrays
                                     */
                                    source.terminalAction { elemSource, elemStart, _ ->
                                        writer.longCopy(elemSource, elemStart)
                                    }
                                }
                            }
                        }
                    }.prependToBlock0(readLength)
                }
            }
            /**
             * Call the callback, or fail
             */
            is DataLayout.SequenceOf -> (sequenceCallback ?: throw UnsupportedOperationException("Hit sequence before length tagged tuple")).invoke(
                layout.sequenceElements, target, l
            )
            is DataLayout.StaticRepeatedOf -> {
                /**
                 * "Allocate" an array, and populate each element recursively.
                 */
                val encodedElemSize = layout.elem.sizeAsEncodedMember()
                return target.startStaticArray(layout.num).foreachElem { i, elemTarget ->
                    l.advanceCurr(encodedElemSize * i.toBigInteger()) { elemStart ->
                        decodeInternal(elemTarget, layout.elem, elemStart, onDecode, null)
                    }
                }
            }
        }
    }
}
