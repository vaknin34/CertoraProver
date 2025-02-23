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

package instrumentation.calls

import analysis.CmdPointer
import analysis.CommandWithRequiredDecls
import analysis.TACCommandGraph
import analysis.icfg.CallInput
import analysis.icfg.CalldataDeterminismHelper
import analysis.maybeNarrow
import bridge.EVMExternalMethodInfo
import com.certora.collect.*
import config.Config
import datastructures.stdcollections.*
import evm.DEFAULT_SIGHASH_SIZE
import evm.DEFAULT_SIGHASH_SIZE_INT
import evm.EVM_WORD_SIZE
import instrumentation.calls.ArgNum.Companion.toArgNum
import report.CVTAlertSeverity
import report.CVTAlertType
import report.CVTAlertReporter
import scene.ICalldataEncoding
import scene.ITACMethod
import tac.CallId
import tac.Tag
import utils.hashObject
import vc.data.*
import vc.data.TACSymbol.Companion.atSync
import vc.data.tacexprutil.TACExprFreeVarsCollector
import java.io.Serializable
import java.math.BigInteger

/**
 * Inclusive [to]
 */
@Treapable
data class CalldataByteRange(val from: BigInteger, val to: BigInteger) : Serializable


/**
 * Represents the number of arguments/parameters in a function's signature.
 * Note: this number does not include the "first four byte" argument, namely the sighash.
 */
@Treapable
sealed class ArgNum : Serializable {

    companion object {
        fun BigInteger.toArgNum() = Known(this)
        val unknown = Unknown
    }

    data class Known(val n: BigInteger) : ArgNum()

    object Unknown : ArgNum() {
        override fun hashCode() = hashObject(this)
        fun readResolve(): Any {
            return Unknown
        }
    }
}

data class CalldataEncoding(
    val calldataBase: TACExpr.Sym.Var = TACExprFactTypeCheckedOnlyPrimitives.Sym(TACKeyword.CALLDATA.toVar()) as TACExpr.Sym.Var,
    val calldataSize: TACExpr.Sym = TACKeyword.CALLDATASIZE.toVar().asSym(),
    val calldataOffset: TACExpr.Sym = TACSymbol.lift(0).asSym(),
    val byteOffsetToScalar: Map<CalldataByteRange, TACSymbol.Var>,
    val argNum: ArgNum,
    val valueTypesArgsOnly: Boolean,
    val sighashSize: BigInteger = DEFAULT_SIGHASH_SIZE
) : ICalldataEncoding, Serializable {
    init {
        check(calldataBase.tag == Tag.ByteMap) { "$calldataBase is with an unexpected tag: ${calldataBase.tag}" }
    }

    companion object {
        /*
          If an upper bound on size of the call data buffer is unknown and we are unable to statically determine the given input's size,
          we bound the long copy into the call data by [maxByteSize] bytes, which are an arbitrarily chosen, "big enough" number of words.
         */
        fun sighashCalldataRange(sighashSize: BigInteger) =
            CalldataByteRange(0.toBigInteger(), sighashSize - BigInteger.ONE)

        fun empty() = CalldataEncoding(
            byteOffsetToScalar = mapOf(),
            argNum = ArgNum.unknown,
            valueTypesArgsOnly = false,
            sighashSize = BigInteger.ZERO
        )

        fun calldataOf(methodCode: CoreTACProgram, evmMethodInfo: EVMExternalMethodInfo? = null): CalldataEncoding {

            val graph = TACCommandGraph(methodCode)
            val calldataScalars = getCalldataScalars(graph)
            val sighashSize = if (evmMethodInfo?.sigHash == null) { BigInteger.ZERO } else { DEFAULT_SIGHASH_SIZE }
            val byteOffsetToScalar: Map<CalldataByteRange, TACSymbol.Var> =
                getByteRangeToScalarMapping(calldataScalars, sighashSize = sighashSize, graph)

            return if (evmMethodInfo != null) {
                CalldataEncoding(
                    byteOffsetToScalar = byteOffsetToScalar,
                    argNum = (evmMethodInfo.argTypes.sumOf { it.getMinimumEncodingSize() } / EVM_WORD_SIZE).toArgNum(),
                    valueTypesArgsOnly = evmMethodInfo.argTypes.all { !it.isDynamicType() },
                    sighashSize = sighashSize
                )
            } else {
                CalldataEncoding(
                    byteOffsetToScalar = byteOffsetToScalar,
                    argNum = ArgNum.unknown,
                    valueTypesArgsOnly = false
                )
            }
        }

        /**
         * Returns a list of successfully scalarized function arguments.
         */
        private fun getCalldataScalars(graph: TACCommandGraph): List<Pair<CmdPointer,TACSymbol.Var>> {
            val toRet = mutableListOf<Pair<CmdPointer,TACSymbol.Var>>()
            graph.commands.forEach { c ->
                if (c.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
                    val rhsVar = c.cmd.rhs.getAs<TACExpr.Sym.Var>()?.s
                    if (rhsVar?.meta?.containsKey(TACMeta.IS_CALLDATA) == true) {
                        toRet.add(c.ptr to rhsVar)
                    }
                }
            }
            return toRet
        }


        /**
         * Returns a mapping of calldata byte ranges to successfully scalarized function arguments.
         */
        private fun getByteRangeToScalarMapping(calldataScalars: List<Pair<CmdPointer,TACSymbol.Var>>, sighashSize: BigInteger, graph: TACCommandGraph):
            Map<CalldataByteRange, TACSymbol.Var> {
            val sortedScalars = calldataScalars.sortedBy { it.second.meta[TACMeta.WORDMAP_KEY]!! }

            fun err() {
                CVTAlertReporter.reportAlert(
                    CVTAlertType.ANALYSIS,
                    CVTAlertSeverity.ERROR,
                    null,
                    "Encountered bad calldata ABI layout for ${graph.name}",
                    null
                )
            }

            return sortedScalars.map { (where, scalar) ->
                val offset = scalar.meta[TACMeta.WORDMAP_KEY]!!

                // if not in offset, and the offset is 32, this is _likely_ to be just a copy from a longcopy.
                // if the block where it appears contains a longcopy from calldata to memory starting copying calldata
                // from a constant offset == 0 we know it's just scalarized from that longcopy and likely to be for proxy patterns
                // we also check the dstOffset is 0 since reserved-space memory write scalarizations are the trigger for the calldata scalarization.
                // (we still prefer to overfit the check)
                if (offset == EVM_WORD_SIZE || offset == EVM_WORD_SIZE * BigInteger.TWO) {
                    if (graph.iterateRevBlock(where).all {
                            it.maybeNarrow<TACCmd.Simple.ByteLongCopy>()?.let {
                                it.cmd.srcBase.meta.containsKey(TACMeta.IS_CALLDATA) && it.cmd.dstBase.meta.containsKey(
                                    TACMeta.EVM_MEMORY
                                )
                                    && it.cmd.srcOffset is TACSymbol.Const && (it.cmd.srcOffset as TACSymbol.Const).value == BigInteger.ZERO
                                    && it.cmd.dstOffset is TACSymbol.Const && (it.cmd.dstOffset as TACSymbol.Const).value == BigInteger.ZERO
                            } != true
                        }) {
                        err()
                        throw IllegalStateException("In ${graph.name}@${where} we saw a calldata read at offset 32, and it could not be related to a scalarized longcopy from calldata to memory, so unlikely to be a proxy pattern?")
                    }
                } else {
                    if (!(offset == BigInteger.ZERO || offset.mod(EVM_WORD_SIZE) == DEFAULT_SIGHASH_SIZE)) {
                        err()
                        throw IllegalStateException("In ${graph.name}@${where}: Invalid offset $offset: it is expected to be either 0 or (n*32)+4")
                    }
                }

                if (sighashSize > BigInteger.ZERO && offset == BigInteger.ZERO) {
                    sighashCalldataRange(sighashSize)
                } else {
                    CalldataByteRange(from = offset, offset + EVM_WORD_SIZE - BigInteger.ONE)
                } to scalar
            }.distinctBy { it.second }.toMap()
        }
    }

    val expectedCalldataSize: BigInteger? =
        when (argNum) {
            is ArgNum.Known -> {
                (this.argNum.n * 32.toBigInteger()) + sighashSize
            }
            is ArgNum.Unknown -> null
        }

    private fun funArgAtOffset(byteOffset: BigInteger): TACExpr {
        check(
            byteOffset == BigInteger.ZERO || (byteOffset >= sighashSize && byteOffset.mod(
                32.toBigInteger()
            ) == sighashSize)
        ) { "Expected to get a valid calldata offset, but instead got $byteOffset" }

        val byteRange = if (byteOffset == BigInteger.ZERO && sighashSize > 0.toBigInteger()) {
            sighashCalldataRange(sighashSize)
        } else {
            CalldataByteRange(byteOffset, byteOffset + 31.toBigInteger())
        }
        return if (byteRange in byteOffsetToScalar) {
            byteOffsetToScalar[byteRange]?.asSym() ?: error("$byteRange is expected to be in $byteOffsetToScalar")
        } else {
            TACExpr.Select(
                calldataBase, CallConvention.addK(calldataOffset, byteOffset)
            )
        }
    }

    // if we have primitive value types, and there is an expected calldatasize, the input size/lower bound
    // cannot be greater
    fun checkInputSizeForArgsOnly(input: CallInput): Boolean =
        Config.DisableInputSizeValidation.get() ||
            (!(this.valueTypesArgsOnly && expectedCalldataSize != null &&
                ((input.size is TACExpr.Sym.Const && input.size.s.value > expectedCalldataSize) ||
                    (input.inputSizeLowerBound != null && input.inputSizeLowerBound > expectedCalldataSize))))

    // if we have dynamic value types, and there is an expected calldatasize, the input size/lower bound
    // cannot be smaller
    // in simpler terms: OR:
    // 1. we have only value types args
    // 2. the expected calldatasize is null
    // 3a. if the input size is known then it's not smaller than the expected calldatasize
    // 3b. AND if the input size lower bound is given then it's not smaller than the expected calldatasize
    fun checkInputSizeForNonArgsOnly(input: CallInput): Boolean =
        Config.DisableInputSizeValidation.get() ||
            (!(!this.valueTypesArgsOnly && expectedCalldataSize != null &&
                ((input.size is TACExpr.Sym.Const && input.size.s.value < expectedCalldataSize) ||
                    (input.inputSizeLowerBound != null && input.inputSizeLowerBound < expectedCalldataSize))))

    fun feedInput(
        input: CallInput,
        callee: ITACMethod
    ): CommandWithRequiredDecls<TACCmd.Simple> {
        val ret = mutableListOf<TACCmd.Simple>()
        val newDecls = mutableSetOf<TACSymbol.Var>()

        check(checkInputSizeForArgsOnly(input))
        {
            "The size of the input ($input) to ${callee.soliditySignature ?: callee.name} is strictly greater than the " +
                "expected size of the calldata buffer (${expectedCalldataSize}). " +
                    "All function arguments are primitives value types."
        }

        check(checkInputSizeForNonArgsOnly(input))
        {
            "Expected the size of the input ($input) to be not smaller than the lower bound of the expected calldata size (${expectedCalldataSize}). " +
                    "The function has a dynamic type argument."
        }

        val inputSizeIsKnown: Boolean =
            input.size is TACExpr.Sym.Const || (this.valueTypesArgsOnly && expectedCalldataSize != null && input.inputSizeLowerBound == expectedCalldataSize)

        val assumeVar = TACKeyword.TMP(Tag.Bool, "Bool")

        if (!inputSizeIsKnown) {
            val refinedInputSizeLowerBound: BigInteger? = input.inputSizeLowerBound

            if (refinedInputSizeLowerBound != null) {
                //[calldataSize] >= [refinedInputSizeLowerBound]
                ret.add(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        assumeVar,
                        TACExpr.BinRel.Ge(calldataSize, TACSymbol.lift(refinedInputSizeLowerBound).asSym())
                    )
                )
                ret.add(TACCmd.Simple.AssumeCmd(assumeVar))
            }
        }

        // calldatasize checks
        // calldatasize
        val calldataSizeEq = TACExpr.BinRel.Eq(
            calldataSize,
            input.size
        ).let { calldatasizeComparison ->
            if (inputSizeIsKnown && input.size !is TACExpr.Sym.Const) {
                TACExpr.BinBoolOp.LAnd(
                    calldatasizeComparison,
                    TACExpr.BinRel.Eq(
                        calldataSize,
                        TACSymbol.Const(expectedCalldataSize!!).asSym()
                    )
                )
            } else {
                calldatasizeComparison
            }
        }
        ret.addAll(
            listOf(
                // calldatasize
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    assumeVar,
                    calldataSizeEq
                ),
                TACCmd.Simple.AssumeCmd(assumeVar)
            )
        )
        newDecls.addAll(TACExprFreeVarsCollector.getFreeVars(calldataSizeEq) + assumeVar)

        // Feed in the first 4 bytes (the function selector), if we know we have a selector,
        // but not if size is known to be 0
        if (sighashSize > BigInteger.ZERO && !(inputSizeIsKnown && input.size.s == TACSymbol.Zero)) {
            TACExpr.BinRel.Eq(
                funArgAtOffset(BigInteger.ZERO),
                input.inputArgAtOffset(BigInteger.ZERO, sighashSize)
            ).let { fourByteEq ->
                ret.addAll(
                    listOf(
                        // first 4 bytes
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(assumeVar, fourByteEq),
                        TACCmd.Simple.AssumeCmd(assumeVar)
                    )
                )
                newDecls.addAll(TACExprFreeVarsCollector.getFreeVars(fourByteEq))
            }
            val calleeSighash = callee.sigHash?.n
            if(calleeSighash != null) {
                val deterministicFor = CalldataDeterminismHelper.deterministicFor(3)
                newDecls.add(deterministicFor)
                newDecls.add(calldataBase.s)
                for (i in 1 until DEFAULT_SIGHASH_SIZE_INT) {
                    val actual = TACExpr.Select(calldataBase, i.asTACExpr)
                    val determinism = TACExpr.Select.buildMultiDimSelect(
                        deterministicFor.asSym(), listOf(
                            i.asTACExpr, input.size, calleeSighash.asTACExpr
                        )
                    )
                    ret.addAll(listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(assumeVar, TACExpr.BinRel.Eq(
                            actual, determinism
                        )),
                        TACCmd.Simple.AssumeCmd(assumeVar)
                    ))
                }
            }
        }

        // Feed in the rest of the input arguments
        /* All arguments that can be handled with scalar assignments, will be handled with the loop.
         * maxScalarRange is the maximal offset of unpacked calldata variables and will be the loop's bound.
         */
        val maxScalarRange =
            byteOffsetToScalar.keys
                .maxByOrNull { it.to }?.to // max for calldata
                ?.max(input.rangeToDecomposedArg.keys.maxByOrNull { it.to }?.to ?: BigInteger.ZERO) // with max from memory
                ?.plus(BigInteger.ONE) // plus 1 (to get the next one to read)
                    ?: BigInteger.ZERO // 0 if null

        // assign all that can by scalars
        assignmentToCalldata(
            maxScalarRange,
            input,
            newDecls,
            ret,
            assumeVar,
            inputSizeIsKnown,
            input.inputSizeLowerBound
        )
        // for the remaining - use a longstore bounded by inputSize (how much we were supposed to write) minus maxScalarRange (how much we wrote with scalars)
        // Better not to issue the longstore if length is definitely 0
        if (!inputSizeIsKnown || input.inputSizeLowerBound // a lower bound size of the input
                ?.minus(maxScalarRange) // not including the max scalar range
                ?.let { sz -> sz > BigInteger.ZERO } // should be strictly greater than 0 to do a longstore
                ?: true) { // or we don't know, and then do a long copy anyway
            val offsetFromStartAfterScalar =   (if (sighashSize > BigInteger.ZERO) {
                sighashCalldataRange(sighashSize).to + BigInteger.ONE
            } else {
                BigInteger.ZERO
            }).max(maxScalarRange)
            assignmentToCalldataByLongCopy(
                input,
                TACExpr.Vec.Add(
                    input.simplifiedOffset ?: input.offset, TACSymbol.lift(offsetFromStartAfterScalar).asSym()),
                TACSymbol.lift(
                    offsetFromStartAfterScalar
                ).asSym(), // copy to original dstOffset + 4
                TACExpr.BinOp.Sub(
                        input.size,
                        TACSymbol.lift(offsetFromStartAfterScalar).asSym()),
            ).let { (cmds, decls) ->
                ret.addAll(cmds)
                newDecls.addAll(decls)
                if (input.simplifiedOffset == null && input.offset.s is TACSymbol.Var) {
                    newDecls.add(input.offset.s as TACSymbol.Var)
                }
            }
        }

        return CommandWithRequiredDecls(ret, newDecls)
    }

    private fun assignmentToCalldataByLongCopy(
        input: CallInput,
        srcOffset: TACExpr,
        dstOffset: TACExpr,
        length: TACExpr,
    ): Pair<List<TACCmd.Simple>, List<TACSymbol.Var>> {
        val longCopy = TACCmd.Simple.AssigningCmd.AssignExpCmd(
            calldataBase.s,
            TACExpr.LongStore(
                calldataBase,
                dstOffset,
                input.baseVar,
                srcOffset,
                length
            )
        )
        return listOf(longCopy) to listOf(calldataBase.s, input.baseVar.s)
    }

    private fun assignmentToCalldata(
        maxSize: BigInteger,
        input: CallInput,
        newDecls: MutableSet<TACSymbol.Var>,
        ret: MutableList<TACCmd.Simple>,
        assumeVar: TACSymbol.Var,
        inputSizeIsKnown: Boolean,
        simplifiedSize: BigInteger?
    ) {
        var offset: BigInteger = sighashSize
        while (offset < maxSize) {
            offset =
                singleAssignmentToCalldata(offset, input, newDecls, ret, assumeVar, inputSizeIsKnown, simplifiedSize)
        }
    }

    private fun singleAssignmentToCalldata(
        offset: BigInteger,
        input: CallInput,
        newDecls: MutableSet<TACSymbol.Var>,
        ret: MutableList<TACCmd.Simple>,
        assumeVar: TACSymbol.Var,
        inputSizeIsKnown: Boolean,
        simplifiedSize: BigInteger?
    ): BigInteger {
        val feedTo = funArgAtOffset(offset)
        val inputArg = input.inputArgAtOffset(offset, sighashSize)
        val eq: TACExpr = TACExpr.BinRel.Eq(
            feedTo, // to callee
            inputArg // from caller
        )

        val assume = TACCmd.Simple.AssumeCmd(assumeVar)

        newDecls.addAll(TACExprFreeVarsCollector.getFreeVars(eq))

        if (!inputSizeIsKnown && (input.inputSizeLowerBound == null || offset >= simplifiedSize)) {
            //NOTE: The second conjunct above entails that if we have assumed that [calldataSize] is at least [input.simplifiedSize],
            // then [offset] is also at least [input.simplifiedSize] (otherwise, it holds that [offset] < [calldataSize]).
            // trg[offset] = src[offset] || offset >= [calldataSize]
            ret.add(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    assumeVar, TACExpr.BinBoolOp.LOr(
                        eq, TACExpr.BinRel.Ge(offset.asTACSymbol().asSym(), calldataSize)
                    )
                )
            )
            ret.add(assume)
        } else if (feedTo is TACExpr.Sym.Var) {
            val eqAsAssignment = TACCmd.Simple.AssigningCmd.AssignExpCmd(
                feedTo.s, inputArg
            )
            ret.add(eqAsAssignment)
        } else {
            ret.add(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    assumeVar, eq
                )
            )
            ret.add(assume)
        }

        return offset + 32.toBigInteger()
    }

    fun copyWithCallId(callId: CallId): CalldataEncoding {
        val baseWithId =  calldataBase.s.atSync(callIndex = callId).asSym()

        val sizeWithId = when (calldataSize) {
            is TACExpr.Sym.Var -> {
                calldataSize.s.at(callIndex = callId).asSym()
            }
            is TACExpr.Sym.Const -> {
                calldataSize
            }
        }
        val offsetWithId = when (calldataOffset) {
            is TACExpr.Sym.Var -> {
                calldataOffset.s.at(callIndex = callId).asSym()
            }
            is TACExpr.Sym.Const -> {
                calldataOffset
            }
        }
        return copy(
            calldataBase = baseWithId,
            calldataOffset = offsetWithId,
            calldataSize = sizeWithId,
            byteOffsetToScalar = byteOffsetToScalar.mapValues { (_, v) -> v.at(callId) })
    }

}
