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

package report.calltrace

import datastructures.stdcollections.*
import evm.DEFAULT_SIGHASH_SIZE
import evm.EVM_BYTES_IN_A_WORD
import evm.EVM_WORD_SIZE
import log.*
import solver.CounterexampleModel
import tac.Tag
import tac.isMapType
import utils.*
import vc.data.*
import vc.data.TACCmd.Simple.AssigningCmd.AssignExpCmd
import vc.data.state.TACValue
import vc.data.tacexprutil.evaluators.TACExprInterpreter
import java.lang.Integer.min
import java.math.BigInteger
import java.util.*
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

private val logger = Logger(LoggerTypes.CALLTRACE)

/**
 * Symbols which are all part of the same calldata/returndata buffer.
 * [buffer] a symbol representing the entire buffer, if one was found. we currently only
 * use this when modeling calldata, and not for returndata.
 * [byteOffsetToScalars] symbols which are scalars of [buffer], indexed by their byte offset into the buffer
 */
class DataFamily {
    var buffer: TACSymbol.Var? = null
        private set
    private val byteOffsetToScalars: MutableMap<BigInteger, TACExpr> = mutableMapOf()

    fun setCalldataBuffer(calldataBuffer: TACSymbol.Var) {
        require(calldataBuffer.isCalldataBuffer()) { "TACSymbol must be a calldata buffer" }

        buffer = calldataBuffer
    }

    fun addScalar(byteOffset: BigInteger, scalar: TACSymbol) {
        require(scalar.tag.isPrimitive()) { "Expected $scalar to have a primitive tag (got ${scalar.tag})" }
        addScalar(byteOffset, scalar.asSym())
    }

    fun addScalar(byteOffset: BigInteger, scalar: TACExpr) {
        require(scalar.tag?.isPrimitive() != false) { "Expected $scalar to have a primitive tag (got ${scalar.tag})" }
        // this is kinda gross!
        if(byteOffset in byteOffsetToScalars && byteOffsetToScalars[byteOffset] is TACExpr.Sym && scalar !is TACExpr.Sym) {
            return
        }
        byteOffsetToScalars[byteOffset] = scalar
    }
    fun addStorageReference(byteOffset: BigInteger, skey: TACSymbol) {
        require(skey.tag.isStorageKey()) { "Expected $skey to be a storage key (got ${skey.tag})" }

        byteOffsetToScalars[byteOffset] = skey.asSym()
    }

    /**
     * Returns a map from the byte offset of this calldata/returndata buffer to a [TACValue] representing
     * the model value in that offset, if such a value exists in [model].
     * [misalignment] is the minimum positive difference between the alignment of the scalar offsets,
     * and the alignment of an [EVM_WORD_SIZE].
     */
    fun toValueMap(model: CounterexampleModel, misalignment: BigInteger): SortedMap<BigInteger, TACValue> {
        val valueMap = sortedMapOf<BigInteger, TACValue>()

        byteOffsetToScalars.forEachEntry { (offset, scalar) ->
            val alignedOffset = offset - misalignment
            if (scalar is TACExpr.Sym.Var && scalar.s in model.havocedVariables) {
                valueMap[alignedOffset] = TACValue.Uninitialized
            }
            val value = try {
                TACExprInterpreter.eval(model, scalar)
            } catch(e: TACExprInterpreter.InterpreterException) {
                logger.info(e) {
                    "Failed to parse $scalar at $offset for buffer ${this.buffer}"
                }
                return@forEachEntry
            }
            valueMap[alignedOffset] = value
        }

        return valueMap
    }
}

/**
 * Models data flow to/from the calldata buffer. Used to construct the [DataFamily] for the calldata.
 */
sealed class CalldataMovement {
    /** A select operation from the map [selectedFrom] at the offset [alignedByteOffset]. */
    data class SelectFromCalldataBuffer(
        val lhs: TACSymbol.Var,
        val alignedByteOffset: BigInteger,
        val selectedFrom: TACSymbol.Var
    ) : CalldataMovement()

    /** Found [scalars] of this [DataFamily.buffer] */
    data class CalldataScalars(val scalars: List<Scalar>) : CalldataMovement() {
        data class Scalar(val byteOffset: BigInteger, val value: TACExpr) {
            constructor(byteOffset: BigInteger, value: TACSymbol) : this(byteOffset, value.asSym())
        }
        constructor(scalar: Scalar): this(listOf(scalar))

        init {
            require(scalars.isNotEmpty()) { "List of scalars cannot be empty" }
        }
    }

    /**
     * Then both sides of the assignment are calldata buffers, which are aliases of each other,
     * but may each come from a different [DataFamily]
     */
    data class CalldataBuffersAlias(val lhsBuffer: TACSymbol.Var, val rhsBuffer: TACSymbol.Var) : CalldataMovement()

    /** The data movement in this assignment is irrelevant to our current model */
    object None : CalldataMovement()

    companion object {
        /** In principle, arbitrary-length arrays might be moved through call data -- setting a reasonable bound here
         * that we still have a chance of displaying with our current means. (we dump these things in full, nothing
         * on-demand or so going on ..) */
        const val MAX_LENGTH_OF_CALLDATA_MOVEMENT_ITEM = 100
    }
}

/** [returnedValue] is stored in the return buffer at the offset [byteAlignedOffset] */
sealed interface WithValue {
    val returnedValue: TACSymbol
    val byteAlignedOffset: BigInteger
}

/** Models data flow to/from the returndata buffer. Used to construct the [DataFamily] for the returndata. */
sealed class ReturndataMovement {
    /**
     * Store from a buffer to a return data buffer.
     *
     * In a Store assign expression,
     * [rhsBuffer] is the base map symbol into which [returnedValue] is being stored at [byteAlignedOffset]
     * [lhsBuffer] is the lhs map symbol
     * thus [lhsBuffer] is the same buffer as [rhsBuffer], possibly except at offset byteAlignedOffset,
     * where the value is returnedValue.
     */
    data class StoreAtReturnBuffer(
        override val returnedValue: TACSymbol,
        override val byteAlignedOffset: BigInteger,
        val rhsBuffer: TACSymbol.Var,
        val lhsBuffer: TACSymbol.Var
    ): ReturndataMovement(), WithValue

    /** Scalars of a return data buffer. */
    data class ReturndataScalar(override val returnedValue: TACSymbol, override val byteAlignedOffset: BigInteger): ReturndataMovement(), WithValue

    data class StorageReference(override val returnedValue: TACSymbol, override val byteAlignedOffset: BigInteger): ReturndataMovement(), WithValue

    object None: ReturndataMovement()

    companion object {
        fun fromReturnWrite(returnedValue: TACSymbol, byteAlignedOffset: BigInteger): ReturndataMovement =
            when {
                returnedValue.tag.isPrimitive() -> ReturndataScalar(returnedValue, byteAlignedOffset)
                returnedValue.tag.isStorageKey() -> StorageReference(returnedValue, byteAlignedOffset)
                else -> None
            }
    }
}

fun SnippetCmd.CVLSnippetCmd.EVMFunctionInvCVLValueTypeArg.calldataMovement(callIndex: Int): CalldataMovement =
    if (this.callIndex == callIndex) {
        CalldataMovement.CalldataScalars(CalldataMovement.CalldataScalars.Scalar(this.calldataOffset, this.calldataSym))
    } else {
        CalldataMovement.None
    }

fun SnippetCmd.EVMSnippetCmd.EVMFunctionReturnWrite.returndataMovement(callIndex: Int): ReturndataMovement =
    if (this.callIndex == callIndex) {
        ReturndataMovement.fromReturnWrite(this.returnValueSym, this.returnbufOffset)
    } else {
        ReturndataMovement.None
    }

/**
 * Best-effort approach to figuring out the shape of calldata.
 * Observes Selects, Stores, and Longstores.
 * For Stores, and Longstores, we assume that if we're storing "into"/"over" a call data map, then we must be setting up
 * call data (Q: would it make sense to just add an extra check that lhs is also call data? is this always the case for
 *  the stores we're interested in??)
 */
fun AssignExpCmd.calldataMovement(model: CounterexampleModel, callIndex: Int): List<CalldataMovement> {
    if (lhs.callIndex == callIndex && lhs.isCalldataBuffer() && rhs.isCalldataBuffer()) {
        return listOf(CalldataMovement.CalldataBuffersAlias(lhsBuffer = lhs, rhsBuffer = rhs.s))
    } else if (rhs is TACExpr.Select && rhs.base.isCalldataBuffer() && rhs.base.s.callIndex == callIndex) {
        val offset = byteOffset(rhs.loc, model)?.expectAlignment(DEFAULT_SIGHASH_SIZE)
        val selectedFrom = rhs.base.s
        if (offset != null) {
            return listOf(CalldataMovement.SelectFromCalldataBuffer(lhs, offset, selectedFrom))
        }
    } else if (rhs is TACExpr.Store && rhs.value is TACExpr.Sym && rhs.base.isCalldataBuffer() && rhs.base.s.callIndex == callIndex) {
        val offset = byteOffset(rhs.loc, model)?.expectAlignment(DEFAULT_SIGHASH_SIZE)
        val sym = rhs.value.s
        if (offset != null) {
            return listOf(CalldataMovement.CalldataScalars(CalldataMovement.CalldataScalars.Scalar(offset, sym)))
        }
    } else if (rhs is TACExpr.LongStore &&  rhs.dstMap.isCalldataBuffer() && rhs.dstMap.s.callIndex == callIndex) {
        val startOffset = byteOffset(rhs.dstOffset, model)?.expectAlignment(DEFAULT_SIGHASH_SIZE)
        // if length exceeds Int range, we don't want to display it anyway (not expecting this to reasonably happen..
        val length = byteOffset(rhs.length, model)?.toIntOrNull()
        if (startOffset != null && length != null) {
            val practicalLength = min(length, CalldataMovement.MAX_LENGTH_OF_CALLDATA_MOVEMENT_ITEM)
            if (length > practicalLength) {
                logger.warn { "Encountered a longstore with a length exceeding the maximum displayable lenght, " +
                    "truncating the displayed data. Statement: $this ; Lenght: $length ; " +
                    "maximal length: ${CalldataMovement.MAX_LENGTH_OF_CALLDATA_MOVEMENT_ITEM}" }
            }
            return ((0 until practicalLength).step(EVM_BYTES_IN_A_WORD)).map { summand ->
                val storeOffset = startOffset + summand
                val storedValue = TACExprFactUntyped { Select(rhs.srcMap, Add(rhs.srcOffset, summand.asTACExpr)) }
                CalldataMovement.CalldataScalars(CalldataMovement.CalldataScalars.Scalar(storeOffset, storedValue))
            }
        }
    } else {
        val symbolsInAssignment = getFreeVarsOfRhs().plus(lhs)
        val scalars = symbolsInAssignment
            .filter { it.calldataCallIndex() == callIndex && it.tag.isPrimitive() }
            .mapNotNull { scalarSym ->
                val offset = scalarSym.calldataOffset()?.expectAlignment(DEFAULT_SIGHASH_SIZE)
                if (offset != null) {
                    CalldataMovement.CalldataScalars.Scalar(offset, scalarSym)
                } else {
                    null
                }
            }

        if (scalars.isNotEmpty()) {
            return listOf(CalldataMovement.CalldataScalars(scalars))
        }
    }

    return emptyList()
}

/**
 * Models data flow from calldata buffers which are actually aliases of each other,
 * or scalars of such buffers.
 */
fun AssignExpCmd.returndataMovement(model: CounterexampleModel): ReturndataMovement {
    if (rhs is TACExpr.Store && rhs.value is TACExpr.Sym && rhs.base is TACExpr.Sym.Var) {
        val offset = when {
            lhs.isReturndata() -> byteOffset(rhs.loc, model)
            else -> this.returnWriteOffset()
        }

        if (offset?.expectAlignment(BigInteger.ZERO) != null) {
            return ReturndataMovement.StoreAtReturnBuffer(rhs.value.s, offset, rhsBuffer = rhs.base.s, lhsBuffer = lhs)
        }
    }

    return ReturndataMovement.None
}

/** update internal state based on calldata movement analysis. */
internal fun CallInputsAndOutputs.registerCalldataMovement(movement: CalldataMovement, callIndex: Int) {
    val family = externalCall(callIndex)?.calldataFamily
    requireNotNull(family) { "cannot register data for uninitialized external call" }

    when (movement) {
        is CalldataMovement.CalldataBuffersAlias -> {
            // ...then these are all aliases of the same calldata buffer.
            val familyBuffer = family.buffer
                ?: run {
                    // then the rhs is a safe candidate for the buffer of the family
                    // note that we will only enter this branch at most once for
                    // each call index.
                    family.setCalldataBuffer(movement.rhsBuffer)
                    movement.rhsBuffer
                }

            aliasingBuffers.union(familyBuffer, movement.rhsBuffer)
            aliasingBuffers.union(movement.lhsBuffer, movement.rhsBuffer)
        }

        is CalldataMovement.SelectFromCalldataBuffer -> {
            // ...then these are scalars from the same calldata buffer.
            // however, before associating these scalars and buffer with the family,
            // we must confirm that the call index matches.
            val familyBuffer =
                if (movement.selectedFrom.calldataCallIndex() == callIndex) {
                    if (family.buffer == null) {
                        family.setCalldataBuffer(movement.selectedFrom)
                    }
                    movement.selectedFrom
                } else {
                    family.buffer?.takeIf { aliasingBuffers.areEqual(it, movement.selectedFrom) }
                }

            if (familyBuffer != null) {
                family.addScalar(movement.alignedByteOffset, movement.lhs)
            }
        }

        is CalldataMovement.CalldataScalars -> {
            //...then these are all scalars of this family.
            for (scalar in movement.scalars) {
                family.addScalar(scalar.byteOffset, scalar.value)
            }
        }

        CalldataMovement.None -> {}
    }
}

/**
 * similar to [registerCalldataMovement], except our (current) modeling is
 * much simpler in this case.
 * in particular, we don't set the [DataFamily.buffer] and we don't use a Union Find.
 */
internal fun CallInputsAndOutputs.registerReturndataMovement(movement: ReturndataMovement, callIndex: Int) {
    val family = externalCall(callIndex)?.returndataFamily
    requireNotNull(family) { "cannot register data for uninitialized external call" }

    when (movement) {
        is ReturndataMovement.ReturndataScalar -> {
            family.addScalar(movement.byteAlignedOffset, movement.returnedValue)
        }

        is ReturndataMovement.StorageReference -> {
            family.addStorageReference(movement.byteAlignedOffset, movement.returnedValue)
        }

        is ReturndataMovement.StoreAtReturnBuffer -> { /* currently unused */ }

        is ReturndataMovement.None -> { }
    }
}

private fun AssignExpCmd.returnWriteOffset() = meta.find(TACMeta.RETURN_WRITE)?.offset

private fun Tag.isStorageKey(): Boolean = this is Tag.UserDefined.UninterpretedSort && name == "skey"

private fun TACSymbol.Var.isCalldata() = meta.containsKey(TACMeta.IS_CALLDATA)
private fun TACSymbol.Var.isReturndata() = meta.containsKey(TACMeta.IS_RETURNDATA)

private fun TACSymbol.Var.isCalldataBuffer() = isCalldata() && tag.isMapType()

@OptIn(ExperimentalContracts::class)
private fun TACExpr.isCalldataBuffer(): Boolean {
    contract {
        returns(true) implies (this@isCalldataBuffer is TACExpr.Sym.Var)
    }
    return this is TACExpr.Sym.Var && this.s.isCalldataBuffer()
}


private fun TACSymbol.Var.calldataOffset() =
    meta.find(TACMeta.CALLDATA_OFFSET)
        ?.also {
            check(isCalldata()) { "Var $this has meta CALLDATA_OFFSET but not IS_CALLDATA" }
        }

// this is returning the right callIndex for variables marked with IS_CALLDATA.
// It works after DSA just fine, because variables with IS_CALLDATA are protected in the second (and critical)
// round of DSA.
// If this is ever to change (the protection of IS_CALLDATA in DSA#2), we'd need to add a meta and get it here instead.
private fun TACSymbol.Var.calldataCallIndex() = callIndex
