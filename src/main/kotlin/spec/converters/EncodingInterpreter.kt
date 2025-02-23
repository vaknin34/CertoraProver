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
import config.Config
import evm.EVM_WORD_SIZE
import evm.EVM_WORD_SIZE_INT
import spec.CodeGenUtils
import spec.converters.DataLayoutInterpreter.Companion.sizeAsEncodedMember
import spec.converters.repr.CVLDataInput
import spec.cvlast.abi.DataLayout
import spec.cvlast.typedescriptors.*
import spec.toProg
import tac.Tag
import vc.data.*
import vc.data.tacexprutil.ExprUnfolder
import java.math.BigInteger
import datastructures.stdcollections.*
import spec.ProgramGenMixin.Companion.andThen

object EncodingInterpreter : DataLayoutInterpreter {
    /**
     * Encode a value in variable [fromVar] into a buffer (represented by [l]) according to the layout [layout].
     */
    fun encode(l: LowLevelEncoder, fromVar: CVLDataInput, layout: DataLayout<EncoderTerminal>) : EncoderOutput {
        return encodeInternal(l, fromVar, layout)
    }
    private fun encodeInternal(l: LowLevelEncoder, fromVar: CVLDataInput, layout: DataLayout<EncoderTerminal>) : EncoderOutput {
        return when(layout) {
            /*
              Follow the dynamic pointer at the current location in the buffer, resolving according to the scope saved somewhere
              up in our callstack
             */
            is DataLayout.DynamicPointer -> {
                l.deref {
                    encodeInternal(it, fromVar, layout.next)
                }
            }
            is DataLayout.OpenScope -> {
                /*
                   save the current location in the buffer for resolving future calls to deref against, (see above)
                 */
                l.saveScope {
                    encodeInternal(it, fromVar, layout.next)
                }
            }
            is DataLayout.Terminal -> {
                /*
                  Perform the movement.
                 */
                when(val t = layout.t) {
                    is TerminalAction.ValueType -> {
                        l.advanceNext(EVM_WORD_SIZE) { reserved ->
                            reserved.terminalAction { buffer, offset, scalar ->
                                fromVar.readPrimitive { srcVar, id ->
                                    val toWrite = TACKeyword.TMP(Tag.Bit256, "!toEncode").toUnique("!")
                                    /*
                                      Convert to Tag.Bit256 according to the encoding in the data layout.
                                     */
                                    val encoding = EVMMoveSemantics.ValueConverters.convertValueTypeToEncoding(
                                        src = srcVar,
                                        dest = toWrite,
                                        destEncoding = t.ty.expectedBufferEncoding
                                    )
                                    /*
                                      Write into the buffer (which expects a bit256)
                                     */
                                    val writeToBuffer = encoding.merge(
                                        CommandWithRequiredDecls(
                                            TACCmd.Simple.AssigningCmd.ByteStore(
                                                base = buffer,
                                                loc = offset,
                                                value = toWrite
                                            )
                                        )
                                    )
                                    /*
                                      And update the scalarized value, again, converting according to encoding.
                                     */
                                    val commands = scalar?.let { scalarVar ->
                                        EVMMoveSemantics.ValueConverters.convertValueTypeToEncoding(
                                            src = srcVar,
                                            destEncoding = t.ty.expectedBufferEncoding,
                                            dest = scalarVar
                                        )
                                    }?.let { writeToScalar ->
                                        writeToBuffer.merge(writeToScalar)
                                    } ?: writeToBuffer
                                    commands.toProg("write primitive", id)
                                }
                            }
                        }
                    }
                    is TerminalAction.Composed -> {
                        /**
                         * The "open" for our existential type. You can't, for god knows what reason, access `t.conv`
                         * directly and have Kotlin realize that value is a ITypeDescriptorConverter. You need
                         * to bind the `*` of `t` to a name (in this case, [I]) have kotlin realize THAT
                         * type is an [ITypeDescriptorConverter]<O, SRC, DST>, and return. Silly!
                         */
                        fun <O, SRC, DST, I> TerminalAction.Composed<O, SRC, DST, I>.unwrap() : ITypeDescriptorConverter<O, SRC, DST>
                            where I : ITypeDescriptorConverter<O, SRC, DST>, I : SupportsSizeQuery = this.conv
                        /**
                         * Simply recurse, converting from [fromVar] to [l] according to the wrapped logic.
                         */
                        t.unwrap().convertTo(
                            cb = { it },
                            toVar = l,
                            fromVar = fromVar
                        ) as EncoderOutput
                    }

                }
            }
            is DataLayout.TupleOf -> {
                val tupleSize = layout.sizeAsEncodedMember()
                /*
                  Reserve size for all the tuple elements
                 */
                l.advanceNext(tupleSize) {
                    val structReader = fromVar.struct<EncoderOutput>()
                    /*
                      For each element...
                     */
                    it.collecting(fromVar.emptyProgram(), layout.elements) { structEncoder, elemInd, elem ->
                        /*
                          structEncoder is just a copy of the outer [it], with the most up-to-date next pointer info.
                          We are encoding [elem] whose index is [elemInd]

                          Compute its offset within the tuple
                         */
                        val fieldOffset = layout.offsetOfField(elemInd)
                        check(fieldOffset < tupleSize)
                        /*
                          Move our current pointer to the field offset within the struct
                         */
                        structEncoder.advanceCurr(fieldOffset) { fieldEncoder ->
                            /*
                              Recurse
                             */
                            structReader.readField(elem.first) { fieldOutput ->
                                encodeInternal(
                                    l = fieldEncoder,
                                    fromVar = fieldOutput,
                                    layout = elem.second
                                )
                            }
                        }
                    }
                }
            }

            is DataLayout.LengthTaggedTuple -> {
                val nxt = when(val e = layout.elems) {
                    is DataLayout.OpenScope -> e.next
                    else -> e
                } as? DataLayout.SequenceOf<EncoderTerminal> ?: throw IllegalStateException("Bad encoding at $layout")
                fun LowLevelEncoder.adjust(f: (LowLevelEncoder) -> LowLevelOutput) : LowLevelOutput = if(layout.elems is DataLayout.OpenScope) {
                    this.saveScope(f)
                } else {
                    f(this)
                }

                val evmElemSize = when(val se = nxt.sequenceElements) {
                    is DataLayout.SequenceElement.Elements -> se.dataLayout.sizeAsEncodedMember()
                    is DataLayout.SequenceElement.PackedBytes1 -> BigInteger.ONE
                }
                fromVar.dynamicArray { len, context, reader ->
                    /**
                     * Compute the total size of the array to "allocate" in the calldata buffer.
                     */
                    val totalSize = TACKeyword.TMP(Tag.Bit256, "TotalSize").toUnique("!")
                    val (elemDataSize, mulCode) = if(evmElemSize == BigInteger.ONE) {
                        CodeGenUtils.wordAlignSymbol(len)
                    } else {
                        val elemDataSize = TACKeyword.TMP(Tag.Bit256, "!elemSize").toUnique("!")
                        elemDataSize to safeMul(elemDataSize, len, evmElemSize.asTACSymbol())
                    }
                    val lengthSanity = ExprUnfolder.unfoldPlusOneCmd("!lengthSanity", TACExpr.BinRel.Lt(len.asSym(), BigInteger.TWO.pow(Config.VMConfig.maxArraySizeFactor).asTACExpr, Tag.Bool)) {
                        TACCmd.Simple.AssumeCmd(it.s)
                    }
                    val addCode = safeAdd(totalSize, elemDataSize, EVM_WORD_SIZE.asTACSymbol())
                    val allocSizeCode = mulCode.merge(addCode).merge(lengthSanity)
                    /**
                     * Advance the next pointer, and then
                     */
                    allocSizeCode andThen l.advanceNext(totalSize) { withEnc ->
                        withEnc.sequencing(fromVar.emptyProgram(), { lenWriter ->
                            /**
                             * Write the length at the current offset, easy!
                             */
                            lenWriter.terminalAction { buffer, offset, scalar ->
                                val writes = CommandWithRequiredDecls(listOfNotNull(
                                    TACCmd.Simple.AssigningCmd.ByteStore(
                                        base = buffer,
                                        loc = offset,
                                        value = len
                                    ),
                                    scalar?.let { _ ->
                                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                            lhs = scalar,
                                            rhs = len
                                        )
                                    }
                                ), setOfNotNull(buffer, offset, scalar))
                                writes.toProg("lenWrite", context)
                            }
                        }, { forElem ->
                            /**
                             * Oh boy hold on to your butts (again!)
                             * Advance the current pointer to the point where the elements begin
                             */
                            forElem.advanceCurrUncheck(EVM_WORD_SIZE) { next ->
                                next.adjust { elemLocation ->
                                    when(val se = nxt.sequenceElements) {
                                        is DataLayout.SequenceElement.Elements -> {
                                            val elemLayout = se.dataLayout
                                            /**
                                             * If we have elements of value type, just long copy
                                             */
                                            if(elemLayout is DataLayout.Terminal && elemLayout.t is TerminalAction.ValueType) {
                                                return@adjust elemLocation.terminalAction { buffer, offset, _ ->
                                                    reader.toOutput { src ->
                                                        CommandWithRequiredDecls(listOf(
                                                            TACCmd.CVL.ArrayCopy(
                                                                src = src,
                                                                elementSize = EVM_WORD_SIZE_INT,
                                                                logicalLength = len,
                                                                dst = TACCmd.CVL.BufferPointer(
                                                                    offset = offset,
                                                                    buffer = TACCmd.CVL.Buffer.EVMBuffer(buffer)
                                                                )
                                                            )
                                                        ), setOf(len, offset, buffer) + src.getReferencedSyms()).toProg("copy", context)
                                                    }
                                                }
                                            }
                                            /** other wise ... */
                                            val encodedSize = elemLayout.sizeAsEncodedMember()

                                            /**
                                             * This is so complicated because of needing to keep track of the distinguished
                                             * next pointer (something something linear types). To accomplish this
                                             * we use callbacks extensively in the [LowLevelEncoder], but that "higher-order"
                                             * programming kind of annoying; we need to build up continuations and then pull
                                             * the pin.
                                             *
                                             * Anyway, this generates call back which expects an encoder,
                                             * and then uses that encoder to write an element at index [ind],
                                             * using the array [reader].
                                             */
                                            fun encodeAtOffset(ind: Int) : (LowLevelEncoder) -> LowLevelOutput {
                                                val offs = ind.toBigInteger() * encodedSize
                                                return { enc ->
                                                    enc.advanceCurrUncheck(offs) { atElemStart ->
                                                        reader.readElem(ind) { elemReader ->
                                                            encodeInternal(
                                                                atElemStart,
                                                                layout = se.dataLayout,
                                                                fromVar = elemReader
                                                            )
                                                        }
                                                    }
                                                }
                                            }

                                            /**
                                             * Given a callback [thenBranch] which, when given an encoder *generates* the `then` branch of a conditional,
                                             * generate a callback which itself accepts an encoder, and then conditionally encodes with [thenBranch]
                                             * if [ind] is within the bounds of the array length [len].
                                             */
                                            fun generateCondition(ind: Int, thenBranch: (LowLevelEncoder) -> LowLevelOutput) : (LowLevelEncoder) -> LowLevelOutput {
                                                val checkVar = TACKeyword.TMP(Tag.Bool, "!indCheck").toUnique("!")
                                                val ifBlock = CommandWithRequiredDecls(listOf(
                                                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                                        lhs = checkVar,
                                                        rhs = TACExpr.BinRel.Lt(ind.asTACExpr, len.asSym(), Tag.Bool)
                                                    )
                                                ), setOf(len, checkVar)).toProg("checkCommand", context)
                                                return { enc: LowLevelEncoder ->
                                                    enc.conditional(context, conditionGen = { then, elseB ->
                                                        ifBlock to TACCmd.Simple.JumpiCmd(
                                                            cond = checkVar,
                                                            dst = then,
                                                            elseDst = elseB
                                                        )
                                                    }) {
                                                        thenBranch(it)
                                                    }
                                                }
                                            }
                                            var ind = Config.LoopUnrollConstant.get() - 1
                                            require(ind >= 0)
                                            /**
                                             * Our accumulator variable. We initialize it with the (callback)
                                             * that generates the conditional that encodes the "last" element.
                                             */
                                            var acc = generateCondition(ind, encodeAtOffset(ind))
                                            ind--
                                            /**
                                             * Our loop invariant is that `acc` always holds the callback which encodes
                                             * all of the iterations (in order) *after* ind.
                                             *
                                             * So, while we still have more iterations to encode...
                                             */
                                            while(ind >= 0) {
                                                /**
                                                 * Did you know that kotlin captures the *mutable reference* of `var`
                                                 * and not their current value? I spent almost a day chasing down
                                                 * a bug due to this...
                                                 *
                                                 * So capture the current values of our accumulator.
                                                 */
                                                val capture = acc
                                                val indCapture = ind
                                                /**
                                                 * Now, update the accumulator to a (callback) which conditionally
                                                 * encodes ind and then executes the current accumulator.
                                                 *
                                                 * For example, ignoring the callbacks of it all, if ind is 1, then we have
                                                 * that acc holds
                                                 * ```
                                                 * if(2 < len) {
                                                 *    ...
                                                 * }
                                                 * ```
                                                 * we then update `acc` to be:
                                                 * ```
                                                 * if(1 < len) {
                                                 *    // encode element 1
                                                 *    if(2 < len) {
                                                 *       ...
                                                 *    }
                                                 * ```
                                                 *
                                                 * We go through all of these hoops because the next pointer at the end
                                                 * of all of this needs to be whatever the *last* iteration outputs.
                                                 */
                                                acc = generateCondition(ind) {
                                                    it.sequencing(
                                                        fromVar.emptyProgram(),
                                                        encodeAtOffset(indCapture),
                                                        capture
                                                    )
                                                }
                                                ind--
                                            }
                                            /**
                                             * From our loop invariant, acc holds (a continuation which generates)
                                             * all iterations "after" ind, which is
                                             * -1, so acc holds all iterations in order after -1, aka 0, 1, ...
                                             *
                                             * So fire off the chain of continuations with [elemLocation]
                                             */
                                            acc(elemLocation).let { toAppend ->
                                                toAppend.mapCVLProgram { prog ->
                                                    /**
                                                     * And then assume the unrolling bound.
                                                     */
                                                    mergeCodes(
                                                        first = prog,
                                                        second = ExprUnfolder.unfoldPlusOneCmd(
                                                            tempVarPrefix = "tmp!",
                                                            expr = TACExprFactTypeCheckedOnlyPrimitives.Le(
                                                                len.asSym(),
                                                                Config.LoopUnrollConstant.get().asTACExpr
                                                            )
                                                        ) {
                                                            TACCmd.Simple.AssumeCmd(it.s)
                                                        }.toProg("check", context)
                                                    )
                                                }
                                            }
                                        }
                                        is DataLayout.SequenceElement.PackedBytes1 -> {
                                            elemLocation.terminalAction { buffer, offset, _ ->
                                                reader.toOutput { source ->
                                                    val tmp = TACKeyword.TMP(Tag.ByteMap, "!zeroMap")
                                                    val zeroDst = TACKeyword.TMP(Tag.Bit256, "!toZero")
                                                    CommandWithRequiredDecls(listOf(
                                                        TACCmd.CVL.ArrayCopy(
                                                            src = source,
                                                            dst = TACCmd.CVL.BufferPointer(
                                                                offset = offset,
                                                                buffer = TACCmd.CVL.Buffer.EVMBuffer(buffer)
                                                            ),
                                                            elementSize = 1,
                                                            logicalLength = len
                                                        ),
                                                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                                            lhs = tmp,
                                                            rhs = TACExpr.MapDefinition(Tag.ByteMap) {
                                                                TACExpr.zeroExpr
                                                            }
                                                        ),
                                                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                                            lhs = zeroDst,
                                                            rhs = TACExpr.Vec.Add(offset.asSym(), len.asSym())
                                                        ),
                                                        /**
                                                         * 0 out the 32 bytes after the end of the bytes array. If these writes
                                                         * "spill over" into the next element, they will be overwritten there
                                                         * (solidity uses a similar trick, but due to our unaligned read
                                                         * problem, we want all indices in this range to be 0)
                                                         */
                                                        TACCmd.Simple.ByteLongCopy(
                                                            srcBase = tmp,
                                                            srcOffset = TACSymbol.Zero,
                                                            length = EVM_WORD_SIZE.asTACSymbol(),
                                                            dstOffset = zeroDst,
                                                            dstBase = buffer
                                                        )
                                                    ), setOf(offset, buffer, len, tmp, zeroDst) + source.getReferencedSyms()).toProg("Copy", context)
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        })
                    }
                }
            }
            is DataLayout.SequenceOf -> throw UnsupportedOperationException("$layout is not in the DataMovementSubset")
            is DataLayout.StaticRepeatedOf -> {
                val reservationSize = layout.num * layout.elem.sizeAsEncodedMember()
                l.advanceNext(reservationSize) { withReservation ->
                    fromVar.staticArray(layout.num) { reader ->
                        val workset = (0..<layout.num.intValueExact()).map { Unit }
                        withReservation.collecting(fromVar.emptyProgram(), workset) { enc, ind, _ ->
                            reader.readElem(ind) { elemReader ->
                                enc.advanceCurr(ind.toBigInteger() * layout.elem.sizeAsEncodedMember()) { elemOut ->
                                    encode(
                                        elemOut, fromVar = elemReader, layout = layout.elem
                                    )
                                }
                            }
                        }
                    }
                }
            }
        }
    }
}
