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
import spec.CVLReservedVariables
import spec.cvlast.typedescriptors.IExternalOutputBuffer
import spec.toVar
import tac.Tag
import vc.data.*
import java.math.BigInteger

typealias LowLevelDecode = CVLTACProgram

/**
 * Decoder analogue of [LowLevelEncoder]. Lke that class, this class has a concept of an internal
 * "current" pointer, but no "next" pointer (as the next pointer is only relevant when encoding).
 */
interface LowLevelDecoder : IExternalOutputBuffer {
    /**
     * Call [f] with a copy of this decoder with the current pointer saved as the point from which
     * dereferences are resolved. It is an error to call this function twice without an intervening
     * call to [deref].
     */
    fun saveScope(f: (LowLevelDecoder) -> LowLevelDecode) : LowLevelDecode

    /**
     * Advance the current pointer by [amount], and invoke [f]. The code to advance the free pointer
     * is prepended onto the return value of [f].
     */
    fun advanceCurr(amount: BigInteger, f: (LowLevelDecoder) -> LowLevelDecode) : LowLevelDecode

    /**
     * Interpret the current location in the buffer as a dynamic offset to be resolved
     * relative to the location saved in [saveScope]. Invokes [f] with a decoder that
     * has advanced the current pointer to the resulting location. The code to advance the current pointer
     * is prepended onto the return value of [f].
     *
     * It is an error to call this function on a decoder that has not had a scope saved with [saveScope].
     */
    fun deref(f: (LowLevelDecoder) -> LowLevelDecode) : LowLevelDecode

    /**
     * Invoke [f] once for each element of [l], passing in the current decoder, the index of the element,
     * and the element itself. The code returned from each invocation of [f] is concatenated and returned.
     */
    fun <R> flatMap(l: List<R>, f: (LowLevelDecoder, Int, R) -> LowLevelDecode): LowLevelDecode

    /**
     * Invoke [f] with the buffer variable, value of the current pointer, and the scalar value corresponding to this
     * constant location (if any).
     */
    fun terminalAction(f: (buffer: TACSymbol.Var, offset: TACSymbol.Var, scalar: TACSymbol.Var?) -> LowLevelDecode): LowLevelDecode

    @Suppress("ClassName")
    companion object {
        private object dummyDecoder : LowLevelDecoder {
            override fun <R> flatMap(
                l: List<R>,
                f: (LowLevelDecoder, Int, R) -> LowLevelDecode
            ): LowLevelDecode {
                return l.mapIndexed { index, r ->
                    f(this, index, r)
                }.reduce(::mergeCodes)
            }

            override fun terminalAction(f: (buffer: TACSymbol.Var, offset: TACSymbol.Var, scalar: TACSymbol.Var?) -> LowLevelDecode): LowLevelDecode {
                val dummyBuffer = CVLReservedVariables.certoraDummy.toVar(Tag.ByteMap).toUnique("!buffer!")
                val dummyInd = CVLReservedVariables.certoraDummy.toVar(Tag.Bit256).toUnique("!offset!")
                val dummySetup = CommandWithRequiredDecls<TACCmd.Spec>(
                    listOf(
                        TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                            lhs = dummyBuffer
                        ),
                        TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                            lhs = dummyInd
                        )
                    ), setOf(dummyBuffer, dummyInd)
                )
                val code = f(dummyBuffer, dummyInd, null)
                return code.prependToBlock0(dummySetup)
            }

            override fun saveScope(f: (LowLevelDecoder) -> LowLevelDecode): LowLevelDecode {
                return f(this)
            }

            override fun advanceCurr(
                amount: BigInteger,
                f: (LowLevelDecoder) -> LowLevelDecode
            ): LowLevelDecode {
                return f(this)
            }

            override fun deref(f: (LowLevelDecoder) -> LowLevelDecode): LowLevelDecode {
                return f(this)
            }

        }

        /**
         * Returns a [LowLevelDecoder] that will provide havoced values and buffers for any location that is not constant
         * offset 0. At offset 0, [symbol] is passed to the terminal action handler.
         */
        operator fun invoke(symbol: TACSymbol) : LowLevelSetup<LowLevelDecoder> {
            /*
               This anonymous class is modeling the ReturnSymCmd, which pretends that a whole buffer is being returned, except the
               only value that can be read from the buffer is the first 32 bytes, i.e., the symbol being returned. Everything else,
               including advancing at all, is modelled conservatively with havoced, non-deterministic values.

               This is an anonymous object instead of a class because unlike the LowLevelDecoderImpl below, we will only create
               one instance per return symbol, so this indicates this is a "one off" object.
             */
            return object : LowLevelDecoder {
                override fun <R> flatMap(
                    l: List<R>,
                    f: (LowLevelDecoder, Int, R) -> LowLevelDecode
                ): LowLevelDecode {
                    return l.mapIndexed { ind, r ->
                        f(this, ind, r)
                    }.reduce(::mergeCodes)
                }

                override fun terminalAction(f: (buffer: TACSymbol.Var, offset: TACSymbol.Var, scalar: TACSymbol.Var?) -> LowLevelDecode): LowLevelDecode {
                    val tmpBuffer = TACKeyword.TMP(Tag.ByteMap, "!dummy").toUnique("!")
                    val offset = TACKeyword.TMP(Tag.Bit256, "!ind").toUnique("!")
                    val mapDefInd = TACKeyword.TMP(Tag.Bit256, "!i").toUnique("!")
                    val scalar = TACKeyword.TMP(symbol.tag, "!asVar").toUnique("!")
                    val setup = CommandWithRequiredDecls(
                        listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = tmpBuffer,
                                rhs = TACExpr.MapDefinition(
                                    listOf(mapDefInd.asSym()),
                                    TACExpr.TernaryExp.Ite(
                                        TACExpr.BinRel.Eq(
                                            mapDefInd.asSym(),
                                            TACSymbol.Zero.asSym(),
                                            Tag.Bool
                                        ),
                                        symbol.asSym(),
                                        TACExpr.Unconstrained(symbol.tag),
                                        symbol.tag
                                    ),
                                    Tag.ByteMap
                                )
                            ),
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = offset,
                                rhs = TACSymbol.Zero.asSym()
                            ),
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = scalar,
                                rhs = symbol.asSym()
                            )
                        ), setOfNotNull(
                            tmpBuffer, symbol as? TACSymbol.Var, scalar, offset
                        )
                    )
                    return f(tmpBuffer, offset, scalar).prependToBlock0(setup)
                }

                override fun saveScope(f: (LowLevelDecoder) -> LowLevelDecode): LowLevelDecode {
                    return f(this)
                }

                override fun advanceCurr(
                    amount: BigInteger,
                    f: (LowLevelDecoder) -> LowLevelDecode
                ): LowLevelDecode {
                    return if(amount != BigInteger.ZERO) {
                        f(dummyDecoder)
                    } else {
                        f(this)
                    }
                }

                override fun deref(f: (LowLevelDecoder) -> LowLevelDecode): LowLevelDecode {
                    return f(dummyDecoder)
                }

            } to CommandWithRequiredDecls(listOf(TACCmd.Simple.NopCmd))
        }

        /**
         * Create a [LowLevelDecoder] for [buffer] with an initial value of the current pointer
         * given by [offset], and with scalar information given by [scalars]. Returns the decoder and the
         * code to initialize the decoder.
         */
        operator fun invoke(
            buffer: TACSymbol.Var,
            offset: TACSymbol,
            scalars: Map<BigInteger, TACSymbol.Var> = mapOf(),
            relativeScalars: Map<BigInteger, TACSymbol.Var> = mapOf()
        ) : LowLevelSetup<LowLevelDecoder> {
            val (pointer, init) = AbstractCodec.initializePointer(
                offset
            )
            return LowLevelDecoderImpl(
                scalars = scalars,
                currPointer = pointer,
                buffer = buffer,
                savedScope = null,
                relativeScalars = relativeScalars
            ) to init
        }
    }
}

private data class LowLevelDecoderImpl(
    val savedScope: BufferPointer?,
    override val currPointer: BufferPointer,
    override val buffer: TACSymbol.Var,
    override val scalars: Map<BigInteger, TACSymbol.Var>,
    override val relativeScalars: Map<BigInteger, TACSymbol.Var>,
) : LowLevelDecoder, AbstractCodec() {
    override fun saveScope(f: (LowLevelDecoder) -> LowLevelDecode): LowLevelDecode {
        require(savedScope == null) {
            "Already saved scope before deref"
        }
        return f(this.copy(
            savedScope = currPointer
        ))
    }

    override fun advanceCurr(amount: BigInteger, f: (LowLevelDecoder) -> LowLevelDecode): LowLevelDecode {
        val (ptr, cmds) = this.currPointer + amount
        return f(this.copy(
            currPointer = ptr
        )).prependToBlock0(cmds)
    }

    override fun deref(f: (LowLevelDecoder) -> LowLevelDecode): LowLevelDecode {
        require(savedScope != null)
        val ptr = this.currPointer.outputPointer
        val relOffset = TACKeyword.TMP(Tag.Bit256, "!RelativeOffset").toUnique("!")
        val read = getScalarLoc()?.let { toDeref ->
            CommandWithRequiredDecls(
                listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = relOffset,
                        rhs = toDeref.asSym()
                    )
                ), setOf(relOffset, toDeref)
            )
        } ?: CommandWithRequiredDecls(
            listOf(
                TACCmd.Simple.AssigningCmd.ByteLoad(
                    lhs = relOffset,
                    loc = ptr,
                    base = this.buffer
                )
            ),
            setOf(relOffset, ptr, this.buffer)
        )
        val (newPointer, addition) = this.savedScope + relOffset
        return f(this.copy(
            savedScope = null,
            currPointer = newPointer
        )).prependToBlock0(read.merge(addition))
    }

    override fun terminalAction(f: (buffer: TACSymbol.Var, offset: TACSymbol.Var, scalar: TACSymbol.Var?) -> LowLevelDecode): LowLevelDecode {
        val scal = getScalarLoc()
        return f(this.buffer, this.currPointer.outputPointer, scal)
    }

    override fun <R> flatMap(l: List<R>, f: (LowLevelDecoder, Int, R) -> LowLevelDecode): LowLevelDecode {
        return l.mapIndexed { i, e ->
            f(this, i, e)
        }.reduce(::mergeCodes)
    }
}
