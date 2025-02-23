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
import spec.CVLCompiler
import spec.cvlast.typedescriptors.IExternalInputBuffer
import spec.toProg
import tac.NBId
import tac.Tag
import vc.data.*
import java.math.BigInteger

typealias LowLevelSetup<T> = Pair<T, CommandWithRequiredDecls<TACCmd.Spec>>
typealias LowLevelOutput = EncoderOutput

/**
 * A low-level interface for encoding values into a buffer, with tracking current/next pointers.
 * As its name suggests, this is pretty low level, and it should almost always be used with the [EncodingInterpreter].
 *
 * The documentation for this class will refer to conceptual "next" and "current" pointers. The "current" pointer
 * points to the location where the current object is being encoded. There may be multiple "current" pointers alive at any
 * given moment, one for each object being encoded. For example, when encoding a struct Foo where:
 *
 * struct Foo { uint x; Bar b }; struct Bar { uint y; uint z; }
 *
 * Then when encoding the `b` field, there will be two current pointers, one pointing to the location where
 * `Foo` is being encoded, an another one pointing 32 bytes "later" in the buffer indicating the position
 * where `b` is being encoded.
 *
 * There is also a distinguished "next" pointer, which points to the next "free" location in the buffer which indicates
 * where the next piece of data should be encoded (hence the name).
 *
 *
 */
interface LowLevelEncoder : IExternalInputBuffer {
    /**
     * Invoke [f] with a copy of this encoder, having saved the current pointer as the location from which to resolve dereferences.
     * The result of [f] is returned directly. It is an error to call this function more than once without
     * an intervening call to [deref].
     */
    fun saveScope(f: (LowLevelEncoder) -> LowLevelOutput) : LowLevelOutput

    /**
     * Call [f] with a copy of this encoder having advanced current pointer [amount]. Before calling
     * this function the next pointer must have been advanced by calling the [BigInteger] variant of [advanceNext],
     * and this function ensures that the amount advanced does not exceed the (static) reservation amount given.
     *
     * The code the effect the current pointer advancement is automatically prepended to the return value of [f].
     */
    fun advanceCurr(amount: BigInteger, f: (LowLevelEncoder) -> LowLevelOutput) : LowLevelOutput

    fun advanceCurrUncheck(amount: BigInteger, f: (LowLevelEncoder) -> LowLevelOutput) : LowLevelOutput

    /**
     * Advance the current pointer to the next pointer location, writing the relative offset into the location
     * of the current pointer (before advancement), and then invoke [f] with the updated
     * encoder. The next pointer must be advanced by calling [advanceNext]
     * and a scope saved via [saveScope] before calling this function. The code to effect the write of the deref
     * is automatically prepended the the output of [f].
     */
    fun deref(f: (LowLevelEncoder) -> LowLevelOutput) : LowLevelOutput

    /**
     * Advance the next pointer the amount given by [amount], and then call [f] with the updated encoder. The code
     * to advance the next pointer is prepended onto the return of [f]. [f] must return as its first component an updated
     * next pointer location (as encapsulated in the [WithOutputPointer] type). It is an error to advance the free pointer
     * on the encoder passed to [f].
     */
    fun advanceNext(amount: TACSymbol.Var, f: (LowLevelEncoder) -> LowLevelOutput) : LowLevelOutput

    /**
     * Advance the next pointer the amount given by [amount], and then call [f] with the updated encoder;
     * as with the [TACSymbol.Var] case, the code to advance the next pointer (if any) is prepended
     * onto the return value of [f]. It is *not* an error to call this version of [advanceNext]
     * multiple times, even interleaved with [advanceCurr], provided the current pointer
     * doesn't go past the "outer most" advanceNext.
     *
     * For example `e.advanceNext(64) { it.advanceCurr(32) { it.advanceNext(32) ... } }` is fine,
     * as the next pointer is advanced 32 bytes relative to the current pointer, which is still less than (or equal to)
     * the first advance next.
     * However, the following will throw an exception:
     *
     * `e.advanceNext(64) { it.advanceCurr(64) { it.advanceNext(32) ... } }`
     */
    fun advanceNext(amount: BigInteger, f: (LowLevelEncoder) -> LowLevelOutput) : LowLevelOutput

    /**
     * Call [f] once for each element of [l]. [f] receives an encoder, the index of the element being encoded,
     * and the element itself. It must return code and an updated next pointer (as encapsulated in [LowLevelOutput]).
     * Each encoder passed to successive calls to [f] is a copy of this encoder, with the next pointer set to the value
     * returned from the previous invocation of [f] (or the initial location of the next pointer, if this is the first invocation).
     *
     * In other words, this function is for sequencing several operations that will update the next pointer.
     */
    fun <R> collecting(empty: CVLTACProgram, l: List<R>, f: (LowLevelEncoder, Int, R) -> LowLevelOutput) : LowLevelOutput

    fun sequencing(empty: CVLTACProgram, vararg f: (LowLevelEncoder) -> LowLevelOutput) : LowLevelOutput = collecting(empty, listOf(*f)) { enc, _, cb ->
        cb(enc)
    }

    fun conditional(
        context: CVLCompiler.CallIdContext,
        conditionGen: (thenBlock: NBId, elseBlock: NBId) -> Pair<CVLTACProgram, TACCmd.Simple.JumpiCmd>,
        thenBranch: (LowLevelEncoder) -> LowLevelOutput
    ) : LowLevelOutput

    /**
     * Invoke the callback [f] with the buffer variable (which is of type [Tag.ByteMap]), the current pointer location,
     * and the scalar variable associated with the constant index into the buffer (if any).
     */
    fun terminalAction(f: (buffer: TACSymbol.Var, offset: TACSymbol.Var, scalar: TACSymbol.Var?) -> CVLTACProgram): LowLevelOutput

    fun unsafeReadNext(): TACSymbol.Var

    companion object {
        /**
         * Construct a [LowLevelEncoder] for a [buffer], with the current pointer initialized to [offset] (which may be a constant), where constant
         * offsets should be written into the variables given in [scalars].
         *
         * Returns a pair of the code to intiailize the encoding process and the encoder itself.
         */
        operator fun invoke(
            buffer: TACSymbol.Var,
            offset: TACSymbol,
            scalars: Map<BigInteger, TACSymbol.Var> = mapOf(),
        ) : LowLevelSetup<LowLevelEncoder> {
            val (pointer, init) = AbstractCodec.initializePointer(offset)
            return LowLevelEncoderImpl(
                savedScope = null,
                buffer = buffer,
                currPointer = pointer,
                scalars = scalars,
                nextPointer = null,
                remainingReservation = null,
                isUnsafePointer = false
            ) to init
        }
    }
}


private data class LowLevelEncoderImpl(
    val savedScope: BufferPointer?,
    val remainingReservation: BigInteger?,
    override val buffer: TACSymbol.Var,
    override val currPointer: BufferPointer,
    val nextPointer: BufferPointer?,
    override val scalars: Map<BigInteger, TACSymbol.Var> = mapOf(),
    val isUnsafePointer: Boolean
) : LowLevelEncoder, AbstractCodec() {
    private val advancedNext : Boolean get() = nextPointer != null

    override val relativeScalars: Map<BigInteger, TACSymbol.Var>
        get() = mapOf()

    override fun saveScope(f: (LowLevelEncoder) -> LowLevelOutput): LowLevelOutput {
        require(savedScope == null) {
            "Already saved scope for encoding operation"
        }
        return f(this.copy(
            savedScope = currPointer
        ))
    }

    override fun advanceCurr(amount: BigInteger, f: (LowLevelEncoder) -> LowLevelOutput): LowLevelOutput {
        require(remainingReservation != null) {
            "Did not reserve a static size before attempting to advance the current pointer"
        }
        require(amount < remainingReservation) {
            "Attempting to reserve past the end of existing static reservation"
        }
        val (newCurr, cmds) = this.currPointer + amount
        val (newNext, fGen) = f(this.copy(
            currPointer = newCurr,
            remainingReservation = this.remainingReservation - amount
        ))
        return (newNext to fGen.prependToBlock0(cmds)).lift()
    }

    override fun advanceCurrUncheck(amount: BigInteger, f: (LowLevelEncoder) -> LowLevelOutput): LowLevelOutput {
        require(advancedNext) {
            "Did not advance next, this is definitely unsafe"
        }
        val (newCurr, cmds) = this.currPointer + amount
        val (newNext, fGen) = f(this.copy(
            currPointer = newCurr,
            isUnsafePointer = true
        ))
        return (newNext to fGen.prependToBlock0(cmds)).lift()
    }

    override fun advanceNext(amount: TACSymbol.Var, f: (LowLevelEncoder) -> LowLevelOutput): LowLevelOutput {
        require(!advancedNext) {
            "Already advanced next"
        }
        val (newNext, cmds) = this.currPointer + amount
        val (output, fGen) = f(this.copy(
            nextPointer = newNext
        ))
        return (output to fGen.prependToBlock0(cmds)).lift()
    }

    override fun advanceNext(amount: BigInteger, f: (LowLevelEncoder) -> LowLevelOutput): LowLevelOutput {
        if(isUnsafePointer) {
            return f(this.copy(remainingReservation = amount))
        }
        require(!advancedNext || (remainingReservation != null && amount <= remainingReservation)) {
            "Already advanced next $amount vs $remainingReservation"
        }
        return if(!advancedNext) {
            val (newNext, codeGen) = this.currPointer + amount
            val (withOut, fGen) = f(this.copy(
                remainingReservation = amount,
                nextPointer = newNext
            ))
            (withOut to fGen.prependToBlock0(codeGen)).lift()
        } else {
            f(this.copy(
                remainingReservation = amount
            ))
        }
    }

    override fun deref(f: (LowLevelEncoder) -> LowLevelOutput): LowLevelOutput {
        check(this.savedScope != null && this.nextPointer != null) {
            "Cannot deref without saving a scope"
        }
        val offset = TACKeyword.TMP(Tag.Bit256, "!PtrOffset").toUnique("!")
        val scalarLoc = getScalarLoc()
        val commands = CommandWithRequiredDecls(
            listOfNotNull(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = offset,
                    rhs = TACExpr.BinOp.Sub(
                        this.nextPointer.outputPointer.asSym(),
                        this.savedScope.outputPointer.asSym()
                    )
                ),
                TACCmd.Simple.AssigningCmd.ByteStore(
                    base = buffer,
                    loc = this.currPointer.outputPointer,
                    value = offset
                ),
                scalarLoc?.let { lhs ->
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = lhs,
                        rhs = offset.asSym()
                    )
                }
            ),
            setOfNotNull(
                scalarLoc,
                offset
            )
        )
        val (output, fGen) = f(this.copy(
            savedScope = null,
            nextPointer = null,
            currPointer = this.nextPointer,
            remainingReservation = null,
            isUnsafePointer = false
        ))
        return (output to fGen.prependToBlock0(commands)).lift()
    }

    override fun terminalAction(f: (buffer: TACSymbol.Var, offset: TACSymbol.Var, scalar: TACSymbol.Var?) -> CVLTACProgram): LowLevelOutput {
        require(this.nextPointer != null) {
            "Can only perform terminal action after setting next pointer"
        }
        return (this.nextPointer to f(buffer, this.currPointer.outputPointer, getScalarLoc())).lift()
    }

    override fun unsafeReadNext(): TACSymbol.Var {
        return nextPointer?.outputPointer ?: throw UnsupportedOperationException("You promised there'd be a next pointer, there wasn't")
    }

    override fun <R> collecting(
        empty: CVLTACProgram,
        l: List<R>,
        f: (LowLevelEncoder, Int, R) -> LowLevelOutput
    ): LowLevelOutput {
        require(this.nextPointer != null)
        var res: CVLTACProgram = empty
        var it = this
        var ind = 0
        for(i in l) {
            val (withOut, cmds) = f(it, ind, i)
            it = this.copy(
                nextPointer = BufferPointer.invoke(withOut)
            )
            ind++
            res = mergeCodes(res, cmds)
        }
        return (it.nextPointer!! to res).lift()
    }

    override fun conditional(
        context: CVLCompiler.CallIdContext,
        conditionGen: (thenBlock: NBId, elseBlock: NBId) -> Pair<CVLTACProgram, TACCmd.Simple.JumpiCmd>,
        thenBranch: (LowLevelEncoder) -> LowLevelOutput
    ): LowLevelOutput {
        require(this.nextPointer != null)
        val res = thenBranch(this)
        val elseBlock = CommandWithRequiredDecls(listOf(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = res.outputPointer,
                rhs = this.nextPointer.outputPointer.asSym()
            )
        ), setOf(res.outputPosition.outputPointer, this.nextPointer.outputPointer)).toProg("cmd", context)
        val thenDest = res.code.getStartingBlock()
        val elseDest = elseBlock.getStartingBlock()
        val (prefix, jump) = conditionGen(thenDest, elseDest)
        return (res.outputPosition to mergeIfCodes(
            prefix,
            jumpiCmd = jump,
            elseCode = res.code,
            thenCode = elseBlock
        )).lift()
    }
}

