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

package analysis.pta.abi

import analysis.*
import analysis.alloc.AllocationAnalysis
import analysis.numeric.*
import analysis.numeric.linear.*
import analysis.numeric.linear.TermMatching.matches
import analysis.pta.*
import analysis.pta.QualifiedInt
import analysis.pta.abi.EncoderAnalysis.SerializedPath.Unresolved
import com.certora.collect.*
import datastructures.stdcollections.*
import evm.DEFAULT_SIGHASH_SIZE
import evm.EVM_WORD_SIZE
import evm.MAX_EVM_UINT256
import log.Logger
import log.LoggerTypes
import tac.Tag
import utils.*
import vc.data.*
import vc.data.tacexprutil.getFreeVars
import java.io.Serializable
import java.math.BigInteger
import java.util.*

private val logger = Logger(LoggerTypes.ABI_ENCODER)

private fun <T> T?.andDebug(f: () -> String) = run {
    logger.debug(f)
    this
}

private fun <T> T.andInfo(f: () -> String) = run {
    logger.info(f)
    this
}

private fun <T> Nothing?.andWarn(f: () -> String) : T? = run {
    logger.warn(f)
    this
}

data class BufferOffset(
    val logicalOffset: BigInteger,
    val hasSighashOffset: Boolean
) {
    val alignment : BigInteger get() = if(hasSighashOffset) {
        DEFAULT_SIGHASH_SIZE
    } else {
        BigInteger.ZERO
    }
}

/**
 * A note on terminology: when we refer to an offset, that offset is always with respect to some
 * (logical) location within a buffer (usually the *physical* index of the beginning of an encoded dynamic object)
 * When we say index, we always mean the physical, absolute index within the encoded buffer.
 */
class EncoderAnalysis(
    private val pointerSem: IPointerInformation,
    private val numeric: NumericAnalysis,
    private val scratchSites: Map<CmdPointer, Optional<BigInteger>>,
    private val allocSites: Map<CmdPointer, AllocationAnalysis.AbstractLocation>,
    private val decoderAnalysis: DecoderAnalysis,
    private val objectPath: ObjectPathAnalysis,
    private val graph: TACCommandGraph
) : ConstVariableFinder, Interpolator, IEncoderAnalysis {

    interface StrideWithIndexing : WithIndexing<ValueQualifier>, StridingQualifier

    data class TopLevelWrite(
        val objectPath: Set<ObjectPath>,
        val const: BigInteger?,
        val isDefinitelyOffset: Boolean,
        val isUnresolvedOffset: Boolean,
    ) : Serializable {
        @Suppress("unused")
        fun transformVariables(f: (TACSymbol.Var) -> TACSymbol.Var) : TopLevelWrite =
            TopLevelWrite(
               const = this.const,
               isUnresolvedOffset = this.isUnresolvedOffset,
               isDefinitelyOffset = this.isDefinitelyOffset,
               objectPath = this.objectPath.map {
                   it.transformVariables(f)
               }.toSet()
            )

        init {
            ptaInvariant(!isUnresolvedOffset || const == null) {
                "Have a top level write that is unresolved, but also has a constant value (how did we know this was a dynamic offset then?)"
            }
        }
    }

    /**
     * An bundle for information about an array:
     *   * the size of it's elements (if it can be determined)
     *   * The paths associated with that array
     */
    private data class SerializedArray(
        /**
         *  if non-null, then the array has elements of size [ElementSize]. Note that a non-null [ElementSize.Bottom]
         *  is different from a null elementsize: if the former case the array is provably empty and thus has no element sizes,
         *  in the latter case the element size could not be inferred.
         */
        val elemMemorySize: ElementSize?,
        val paths: Set<ObjectPath>?
    )

    /**
     * Given a variable that we suspect corresponds to the start of an array, extract information about it as
     * represented by a [SerializedArray] object.
     *
     * Two sources are checked, first we see if the variable is a dynamic start object being decoded (as recorded
     * in the decoder analysis state). Otherwise we check the pointer analysis for an in-memory array.
     */
    private fun getArrayInfo(arrayVar: TACSymbol.Var, whole: PointsToDomain) : SerializedArray {
        return whole.decoderState.qualifiers[arrayVar]?.let {
            it as? DecoderAnalysis.AbstractDomain.BufferIndices.DynamicStart
        }?.takeIf {
            it.knownType is ArrayType && it.mustBeArray
        }?.let {
            val arrT = (it.knownType as ArrayType)
            val elemSize = if(arrT is HeapType.ByteArray) {
                BigInteger.ONE
            } else {
                EVM_WORD_SIZE
            }
            SerializedArray(
                    elemMemorySize = ElementSize.Concrete(elemSize),
                    paths = decoderAnalysis.getCalldataArrayPaths(arrayVar, whole)
            )
        } ?: SerializedArray(
                pointerSem.getElementSizeOrEmpty(arrayVar, whole.pointsToState),
                objectPath.getPathOf(arrayVar, whole)
        )
    }

    /**
     * The "path" associated with a dynamic object. The encoding process does not (directly!)
     * provide information about which object is being encoded. We must infer the (memory) object being encoded by
     * observing the object paths that are written into the buffer. However, there are two problems:
     *
     * 1) Multiple dynamic objects may be "created" within the buffer before any paths are written, and
     * 2) (More seriously) the paths being written are ambiguous.
     *
     * Consider, for example, a struct defined as follows:
     * struct Foo {
     *    Bar bar;
     *    uint foo;
     * }
     * struct Bar {
     *    uint[] arr;
     * }
     *
     * And we see a top-level write of 32 at index 0, followed by a top-level write of 64 at index 32.
     * This could represent one of three situations:
     * + we are encoding the constant 32 followed by an instance of Bar OR
     * + We are encoding an instance of Foo (in which case the 32 is the offset to the beginning of Foo, and 64 is the offset
     * to the beginning of Bar relative to the beginning of Foo).
     * + We are just writing 32 followed by 64
     *
     * We can't resolve this ambiguity at the point we write these constants, similarly, if we have a known dynamic start
     * but have yet to write any object paths, we don't know what object the dynamic start is being encoded for. Until
     * we can resolve the dynamic object's identity, we use the [Unresolved] constructor to remember the paths from some
     * constant, root index through some number of fields.
     *
     * Q: Don't you have to remember traversals through array objects?
     * A: No, we can always immediately resolve ambiguity the first time we see an array length write, so we will
     * never have an unresolved, ambiguous path that involves an array, only struct fields.
     *
     * Q: What if you start writing elements before writing the array's length?
     * A: We assume this never happens :)
     */
    sealed class SerializedPath {
        data class Unresolved(val root: BigInteger, val fields: List<BigInteger>) : SerializedPath() {
            infix operator fun plus(f: BigInteger) = this.copy(fields = this.fields + f)

        }
        data class Resolved(val o: ObjectPath) : SerializedPath()
    }

    override val encodeCompletePoints = mutableMapOf<CmdPointer, IEncoderAnalysis.EncodeCompletePoint>()

    private fun HeapType.structLevels(): Int {
        return when (this) {
            is HeapType.OffsetMap -> 1 + this.fieldTypes.values.maxOf { it.structLevels() }
            else -> 0
        }
    }

    override fun rootTypes(topLevelWrite: TopLevelWrite, whole: PointsToDomain): List<Pair<HeapType, ObjectPath>>? {
        return topLevelWrite.objectPath.mapNotNull {
            when (val r = it.root) {
                is ObjectPathAnalysis.ObjectRoot.CalldataRoot -> decoderAnalysis.getCalldataRootType(r)?.recursiveResolution()
                is ObjectPathAnalysis.ObjectRoot.V -> pointerSem.getHeapType(loc = r.v, pState = whole)?.recursiveResolution()
            }?.to(it)
        }.takeIf {
           it.isNotEmpty()
        }?.sortedByDescending {
            it.first.structLevels()
        }
    }

    override fun toEncodedValue(topLevelWrite: TopLevelWrite, whole: PointsToDomain): TopLevelValue {
        if(topLevelWrite.isDefinitelyOffset) {
            ptaInvariant(topLevelWrite.objectPath.isNotEmpty()) {
                "Have a dynamic offset $topLevelWrite, but we never resolved it"
            }
        }
        if(topLevelWrite.objectPath.isNotEmpty()) {
            val inferredType = topLevelWrite.objectPath.mapNotNull {
                it as? ObjectPathGen.Root
            }.monadicMap {
                when (it.oRoot) {
                    is ObjectPathAnalysis.ObjectRoot.CalldataRoot -> decoderAnalysis.getCalldataRootType(it.oRoot)
                    is ObjectPathAnalysis.ObjectRoot.V -> pointerSem.getHeapType(loc = it.oRoot.v, pState = whole)
                }
            }?.monadicFold { h1: HeapType, h2: HeapType ->
                if (!h1.checkCompatibility(h2)) {
                    null
                } else {
                    h1.join(h2)
                }
            }
            ptaInvariant(inferredType != null) {
                "Top level write $topLevelWrite does not have a coherent type for its paths ${topLevelWrite.objectPath}"
            }
            return TopLevelValue.Path(
                ty = inferredType,
                paths = topLevelWrite.objectPath,
                encodedPartitions = null
            )
        } else {
            ptaInvariant(topLevelWrite.const != null && !topLevelWrite.isDefinitelyOffset) {
                "Top-level write $topLevelWrite expected to be a regular constant: it isn't"
            }
            return TopLevelValue.Constant(
                k = topLevelWrite.const
            )
        }
    }

    override fun kill(e_: State, killedBySideEffects: Set<TACSymbol.Var>): State {
        return State(
            finalizedState = e_.finalizedState.retainAllKeys {
                it !in killedBySideEffects
            },
            encoding = e_.encoding?.let { e ->
                killedBySideEffects.fold(e, EncodingState::kill)
            }
        )
    }

    data class FinalizedBuffer(
        val buffer: Map<BigInteger, TopLevelWrite>
    )

    /**
     * State of the analysis. One of the two components is always populated,
     * [finalizedState]: which maps variables holding buffers to the encoding result.
     *
     * The other component, [encoding] tracks the currently processing encoding (we assume only one buffer
     * is being encoded at any time). If there is no encoding (or something has gone wrong during the analysis
     * of an encoding scheme) [encoding] is null
     */
    data class State(
        val encoding: EncodingState?,
        val finalizedState: TreapMap<TACSymbol.Var, FinalizedBuffer>
    ) {
        fun join(parentAnalysis: EncoderAnalysis, other: State, thisContext: PointsToDomain, otherContext: PointsToDomain) : State {
            return State(
                    encoding = this.encoding?.let { a ->
                        other.encoding?.let { b ->
                            a.join(parentAnalysis, b, thisContext = thisContext, otherContext = otherContext)
                        }
                    },
                    finalizedState = this.finalizedState.pointwiseBinopOrNull(other.finalizedState) { a, b ->
                        // This could be refined but, meh
                        a.takeIf { a == b }
                    }
            )
        }

        companion object {
            val empty = State(
                    encoding = null,
                    finalizedState = treapMapOf()
            )
        }
    }

    /**
     * Tracks root writes: as described (TODO: ELSEWHERE), in some cases solidity may write an offset
     * into a field, and then add that offset to the dynamic start object containing the field, yielding the
     * dynamic start of a child object.
     *
     * We have to handle this case for the root as well: for example, we may write variable x to index 36 in the root,
     * and then add x to z, where z is a pointer at index 4 within the buffer (i.e., it is the beginning of the encoded
     * calldata). In that case, we should assume that the x is the offset of a fresh dynamic object whose root is encoded
     * at index 36.
     */
    data class RootOffsetWrite(
        val symbol: TACSymbol.Var,
        val logicalField: BigInteger,
        val baseVariables: Set<TACSymbol.Var>
    )

    data class MCopyOperands(
        val srcOffset: TACSymbol.Var,
        val srcLength: TACSymbol
    )

    /**
     * The real heart of the analysis. Like the decoder analysis, it maintains a map of variables to qualifiers:
     * these qualifiers are related to the encoding of objects into the buffer represented by [buffer] (as stated elsewhere,
     * we only support encoding into a single buffer at a time).
     *
     * When encoding into a buffer, it is important to precisely track which physical object is the "last" in the buffer.
     * This information is important for determining where to place the "next" object to encode. Note that the "next" object
     * may be unrelated to whatever object is currently being encoded, for example, when encoding two, unrelated arrays
     * into a buffer, the second array must be placed at the location after the first array.
     *
     * Accordingly, this state tracks which [analysis.pta.abi.EncoderAnalysis.ValueQualifier.OffsetQualifier.DynamicStart]
     * object is the last (i.e., most recently encoded) object in the buffer. When the analysis detects that the encoding
     * has computed the *end* position of the object pointed to by [currPointer], it will record the variable
     * holding that end position in [nextPointer], i.e., the variable holding the end location of the [currPointer] becomes
     * the location where the "next" object is to be placed. Note that [currPointer] and [nextPointer] may not be non-null
     * at the same time. A non-null [currPointer] indicates that we know which object is the most recent, but we don't
     * know it's end point yet. As soon as we compute it's end point, we clear [currPointer] and set [nextPointer] to
     * be non-null.
     *
     * As described in the documentation for [RootOffsetWrite], the solidity compiler may write an (apparently unrelated,
     * unqualified) symbol into a field, where that symbol is *later* used as an offset to a child dynamic object.
     * Usually we do not allow writing untracked, unqualified values into fields unless we know it is an offset.
     * However to support this unfortunate pattern generated by the compiler, we need briefly allow breaking that rule,
     * provided the very next operation we observe is the computation of a child, dynamic start offset using the
     * offset last read, see [analysis.pta.abi.EncoderAnalysis.ValueQualifier.OffsetQualifier.DynamicStart.lastWrittenOffset].
     * The [expectNext] indicates that we expect to see a computation of the next pointer using the last written offset
     * in some dynamic start.
     *
     * [varRoots] map constant, "top-level" writes (i.e., at constant indices into the beginning of the buffer) to the
     * corresponding [TopLevelWrite]. To support top-level static arrays, we also track striding with [rootStrides].
     *
     * [lastRootWrite] serves the same role as [analysis.pta.abi.EncoderAnalysis.ValueQualifier.OffsetQualifier.DynamicStart.lastWrittenOffset]
     * but for the root of the buffer: there is no DynamicStart qualifier associated with the root, so we have to record
     * that information somewhere, and as the root is shared across the entire encoding process, we use the [EncodingState]
     * for that purpose.
     *
     * Finally, [expectNextWriteZero] is indicates to the analysis that we expect to see a write of zero to
     * clear unused bytes when encoding bytes arrays. i.e., the analysis checks this flag when it sees a write
     * of zero and if it is set, it simply ignores the write and continues. The analysis will also fail if
     * it does _not_ see a zero write where it definitely expected to see one.
     *
     * [rootAlignment] indicates whether we expect all of the root elements to be offset by the given amount if non-null.
     * If this field is null, we have no inferred the expected alignment yet. Once set, this alignment cannot be changed, and
     * it is an error to access a buffer in a way that is inconsistent.
     *
     * [copyBuffers] is used to record "staged" mcopy operations. If we see a long copy from memory into an mcopy buffer,
     * we associate the mcopy buffer (the [Tag.ByteMap] variable) with the [MCopyOperands], which records the variables
     * used as the "source" of the mcopy (as we later expect to see a copy out of the mcopy buffer to some other
     * location in memory)
     */
    data class EncodingState(
        val nextPointer: TACSymbol.Var?,
        val currPointer: TACSymbol.Var?,
        val qualifiers: TreapMap<TACSymbol.Var, ValueQualifier>,
        val buffer: WritablePointer,
        val expectNext: Boolean,
        val varRoots: TreapMap<BigInteger, TopLevelWrite>,
        val rootStrides: TreapMap<StridePath, TreapSet<ObjectPath>>,
        val expectNextWriteZero: ExpectNextWriteZero,
        val lastRootWrite: RootOffsetWrite?,
        val rootAlignment: BigInteger?,
        val copyBuffers: TreapMap<TACSymbol.Var, MCopyOperands>
    ) : ConstVariableFinder {

        fun resolveAlignment(
            newAlignment: BigInteger
        ) : EncodingState? {
            return if(this.rootAlignment == null) {
                this.copy(
                    rootAlignment = newAlignment
                )
            } else if(this.rootAlignment != newAlignment) {
                null
            } else {
                this
            }
        }

        /**
         * A 3-valued representation of whether to expect a zero write following
         * a long copy.
         *
         * A zero write is necessary after a long copy in case we wrote a non-multiple-of-EVM_WORD_SIZE
         * bytes, and need to zero out the rest of a partially-written word.
         */
        enum class ExpectNextWriteZero {
            /* We saw a definitely not-multiple-of-EVM_WORD_SIZE longcopy */
            Required,
            /* We saw a definitely multiple-of-EVM_WORD_SIZE longcopy */
            Optional,
            /* We did not see a longcopy */
            NotExpected,
            ;

            infix fun and(o: ExpectNextWriteZero): ExpectNextWriteZero =
                if (this == o) {
                    this
                } else {
                    NotExpected
                }
        }

        companion object : ConstVariableFinder {
            fun init(c: WritablePointer) : EncodingState {
                return EncodingState(
                    nextPointer = null,
                    currPointer = null,
                    qualifiers = treapMapOf(),
                    buffer = c,
                    expectNext = false,
                    varRoots = treapMapOf(),
                    rootStrides = treapMapOf(),
                    expectNextWriteZero = ExpectNextWriteZero.NotExpected,
                    lastRootWrite = null,
                    rootAlignment = null,
                    copyBuffers = treapMapOf()
                )
            }

            private fun <T> T?.equalityJoin(other: T?) : T? {
                return if(this == null) {
                    other
                } else if(other == null) {
                    this
                } else {
                    this.takeIf { it == other }
                }
            }

            private fun joinQualifier(
                buffer: WritablePointer,
                k: TACSymbol.Var,
                left: ValueQualifier?,
                leftState: PointsToDomain,
                right: ValueQualifier?,
                rightState: PointsToDomain,
                parentAnalysis: EncoderAnalysis
            ) : ValueQualifier? {
                if(left == null && right == null) {
                    return null
                }
                if(left == null && right != null) {
                    return joinQualifier(buffer = buffer, k = k, left = right, leftState = rightState, right = left, rightState = leftState, parentAnalysis = parentAnalysis)
                }
                if(left is FieldPointer && right is StridingQualifier) {
                    ptaInvariant(right !is FieldPointer) {
                        "extremely surprising type hierarchy $right is Striding pointer and Field pointer!"
                    }
                    return joinQualifier(buffer = buffer, k = k, left = right, leftState = rightState, right = left, rightState = leftState, parentAnalysis = parentAnalysis)
                }
                if(left is ElemPointer && right is StridingQualifier) {
                    return joinQualifier(
                        buffer = buffer,
                        k = k,
                        left = right,
                        leftState = rightState,
                        right = left,
                        rightState = leftState,
                        parentAnalysis = parentAnalysis
                    )
                }
                if(left is FieldPointer && right is ValueQualifier.OffsetQualifier.DynamicStart) {
                    @Suppress("KotlinConstantConditions")
                    ptaInvariant(right !is FieldPointer) {
                        "extremely surprising type hierarchy: $right is a Dynamic start *and* a field pointer"
                    }
                    return joinQualifier(buffer = buffer, k = k, left = right, leftState = rightState, right = left, rightState = leftState, parentAnalysis = parentAnalysis)
                }
                if(left is ValueQualifier.RootQualifier && right is ValueQualifier.OffsetQualifier) {
                    return joinQualifier(buffer = buffer, k = k, left = right, leftState = rightState, right = left, rightState = leftState, parentAnalysis = parentAnalysis)
                }
                if(right is ValueQualifier.OffsetQualifier.EncodedFieldPointer && left is ElemPointer) {
                    return joinQualifier(
                        buffer = buffer,
                        k = k,
                        left = right,
                        leftState = rightState,
                        right = left,
                        rightState = leftState,
                        parentAnalysis = parentAnalysis
                    )
                }
                check(left != null) {
                    "While joining, left was null? (right was $right)"
                }
                return when (left) {
                    is ValueQualifier.OffsetQualifier.EncodedFieldPointer -> {
                        if(right is ValueQualifier.OffsetQualifier.EncodedFieldPointer) {
                            if (left.parent != right.parent) {
                                return null
                            }
                            return if (left.offset == right.offset) {
                                left.copy(
                                        indexVars = right.indexVars.intersect(left.indexVars)
                                )
                            } else {
                                StridingQualifier.joinMismatchedField(left.offset, leftState, right.offset, rightState) { stridePath, strideBy, index ->
                                    ValueQualifier.OffsetQualifier.DynamicStridePointer(
                                            parent = left.parent,
                                            innerOffset = BigInteger.ZERO,
                                            stridePath = stridePath,
                                            strideBy = strideBy,
                                            indexVars = index
                                    )
                                }
                            }
                        } else if(right is ValueQualifier.RootQualifier.RootFieldPointer) {
                            /**
                             * As described (TODO: elsewhere), it is possible that a root field
                             * is "promoted" to a dynamic start based on inferred dynamic paths. In that case,
                             * we may get a domain mismatch, i.e., at the top of a loop, where at entrance we assumed
                             * that a variable held a root field, but within the loop we deduced it was actually a start.
                             *
                             * In this case, we check to see whether the constant values recorded at constant indices
                             * within the buffer in the state where we have a [analysis.pta.abi.EncoderAnalysis.ValueQualifier.RootQualifier.RootFieldPointer]
                             * are consistent with the deduced placement of the DynamicStart. If so, we keep our
                             * [analysis.pta.abi.EncoderAnalysis.ValueQualifier.OffsetQualifier.EncodedFieldPointer],
                             * or promote to a [analysis.pta.abi.EncoderAnalysis.ValueQualifier.OffsetQualifier.DynamicStridePointer]
                             * as explained below.
                             */
                            leftState.encoderState.encoding?.qualifiers?.get(left.parent)?.let {
                                it as? ValueQualifier.OffsetQualifier.DynamicStart
                            }?.let {
                                /**
                                 * Why are we subtracting the offsets from each other? They refer to different
                                 * kinds of offset (in the right case, the absolute index within a buffer,
                                 * in the left case, the relative offset w.r.t. some dynamic start)!
                                 *
                                 *
                                 * Don't panic: recall that [left] is an EncodedField pointer, which means that if [right] is
                                 * supposed to represent the same thing, it is itself should be an offset from a dynamic start.
                                 * Note that in this case, [right]'s "dynamic" start would actually begin at a constant, absolute
                                 * index within the encoded buffer. Further, we know that because left and right should represent
                                 * "the same thing", [right]'s offset RELATIVE to its dynamic start parent must be the same
                                 * as [left]'s. Thus, we expect that [right]'s dynamic start parent must occur at the (constant, absolute)
                                 * index given by [right].offset - [left].offset.
                                 */
                                if(right.offset > left.offset && parentAnalysis.isDynamicStartConsistent(
                                                dynamicObject = it,
                                                dynamicState = leftState,
                                                /* Again, the absolute index of where we expect to find right's corresponding dynamic parent */
                                                rootOffset = right.offset - left.offset,
                                                rootState = rightState
                                        )) {
                                    left

                                /**
                                 * So how else could we have this mismatch if right is not also field offset.
                                 *
                                 * Well, it is possible that we are in a loop, where [right] was initially assumed to be
                                 * a root field, but within the loop we determined it was a dynamic start. Further, if the loop
                                 * itself is actually iterating over a static array (which has dynamic contents) then
                                 * when we come back around:
                                 * 1. The iteration pointer will be an encoded field offset, and
                                 * 2. the pointer from the initial state will still be a regular old root offset.
                                 *
                                 * (Note that when we usually see such a loop over a static array, we are joining two mismatched
                                 * fields of the same "sort", i.e. EncodedFieldOffets or RootFieldOffsets, this is a very special case
                                 * where that is not true)
                                 *
                                 * So we: check to see if the absolute index represented by [right] is consistent with the start
                                 * of the dynamic object that is left's parent, and then we assume that we are seeing a stride
                                 * from that pointer, the size of which is just [left]'s offset. This immediate
                                 * promotion to a dynamic stride pointer is really equivalent to first promoting [right] to a dynamic start,
                                 * and then redoing the join (which would yield the a dynamic stride pointer), but we
                                 * collapse the steps here.
                                 */
                                } else if(parentAnalysis.isDynamicStartConsistent(
                                                dynamicObject = it,
                                                dynamicState = leftState,
                                                rootOffset = right.offset,
                                                rootState = rightState
                                        )) {
                                    ValueQualifier.OffsetQualifier.DynamicStridePointer(
                                            parent = left.parent,
                                            indexVars = leftState.variablesEqualTo(BigInteger.ONE).intersect(
                                                    rightState.variablesEqualTo(BigInteger.ZERO)
                                            ).toSet(),
                                            stridePath = StridePath(root = BigInteger.ZERO, path = listOf()),
                                            strideBy = left.offset,
                                            innerOffset = BigInteger.ZERO
                                    )
                                } else {
                                    null
                                }
                            }
                        } else if(right is ElemPointer && right.parent == left.parent) {
                            StridingQualifier.joinMismatchedField(k1 = left.offset, s1 = leftState, k2 = BigInteger.ZERO, s2 = rightState) { path, strideBy, ind ->
                                ValueQualifier.OffsetQualifier.DynamicStridePointer(
                                    indexVars = ind,
                                    parent = right.parent,
                                    innerOffset = BigInteger.ZERO,
                                    strideBy = strideBy,
                                    stridePath = path
                                )
                            }
                        } else {
                            return null
                        }
                    }
                    is ValueQualifier.OffsetQualifier.DynamicStridePointer -> {
                        if(right is ValueQualifier.OffsetQualifier.EncodedFieldPointer) {
                            if(right.parent != left.parent) {
                                return null
                            }
                            return StridingQualifier.joinStridingAndField(left, right)
                        } else if(right is ValueQualifier.OffsetQualifier.DynamicStridePointer) {
                            if (left.parent != right.parent) {
                                return null
                            }
                            return StridingQualifier.joinStridePaths(left, right) { a, b -> a.copy(stridePath = b) }
                        } else if(right is ElemPointer) {
                            if(right.parent != left.parent) {
                                return null
                            }
                            return StridingQualifier.joinStridingAndField(left, object : FieldPointer {
                                override val offset: BigInteger
                                    get() = BigInteger.ZERO

                            })
                        } else if(right is ValueQualifier.RootQualifier.RootFieldPointer) {
                            /**
                             * This case is like a mashup of the two cases see above in the [analysis.pta.abi.EncoderAnalysis.ValueQualifier.OffsetQualifier.EncodedFieldPointer]
                             * and [analysis.pta.abi.EncoderAnalysis.ValueQualifier.OffsetQualifier.DynamicStridePointer]
                             * cases. As before, the assumption is that [right] is actually an EncodedField relative
                             * to some dynamic start (which, despite the name, is at a constant, absolute index).
                             * However, because [left] is a dynamic stride pointer, to find the parent we must
                             * subtract the offset to the FIRST element in our stride path, this is computed
                             * by [toFirstElem]. Then, we check consistency against the inferred absolute offset
                             * offset of right's parent, and if the consistency holds, we proceed with [left] as the result
                             * of the join. Note that again, this is equivalent to first promoting [right] to an EncodedField
                             * pointer and then restarting the join with [left], but this restarted join would just yield [left],
                             * so we use this result directly.
                             */
                            val untilStart = left.toFullPath().path.toFirstElem(left.stridePath.root)
                            if(untilStart > right.offset) {
                                return null
                            }
                            val dynamicObject = leftState.encoderState.encoding?.qualifiers?.get(left.parent)?.let {
                                it as? ValueQualifier.OffsetQualifier.DynamicStart
                            } ?: return null
                            return if(!parentAnalysis.isDynamicStartConsistent(
                                            dynamicState = leftState,
                                            dynamicObject = dynamicObject,
                                            rootState = rightState,
                                            rootOffset = right.offset - untilStart
                                    )) {
                                null
                            } else {
                                left
                            }
                        } else {
                            return null
                        }
                    }
                    is ValueQualifier.RootQualifier.RootFieldPointer -> {
                        if(right == null) {
                            /**
                             * Is right actually at a constant index within the buffer?
                             */
                            val buffOffset = rightState.getOffsetFor(buffer, k) ?: return null
                            ptaInvariant(leftState.encoderState.encoding?.rootAlignment != null) {
                                "Created root field pointer in left state but don't have an alignment yet?"
                            }
                            if(buffOffset.alignment != leftState.encoderState.encoding?.rootAlignment) {
                                logger.warn {
                                    "Joining encoder states, have different root alignments ${buffOffset.alignment} vs ${leftState.encoderState.encoding?.rootAlignment}"
                                }
                                return null
                            }
                            val offset = buffOffset.logicalOffset
                            /**
                             * If the offsets are equal, then we use [left] directly
                             */
                            if(offset == left.offset) {
                                return left
                            }
                            /**
                             * Otherwise this is a mismatch, and thus a stride
                             */
                            return StridingQualifier.joinMismatchedField(left.offset, leftState, offset, rightState) { stridePath, strideBy, ind ->
                                ValueQualifier.RootQualifier.RootStridePointer(
                                        strideBy = strideBy,
                                        stridePath = stridePath,
                                        innerOffset = BigInteger.ZERO,
                                        indexVars = ind
                                )
                            }
                        } else if(right is ValueQualifier.RootQualifier.RootFieldPointer) {
                            if(right.offset == left.offset) {
                                return right
                            }
                            return StridingQualifier.joinMismatchedField(left.offset, leftState, right.offset, rightState) { stridePath, strideBy, ind ->
                                ValueQualifier.RootQualifier.RootStridePointer(
                                        stridePath = stridePath,
                                        strideBy = strideBy,
                                        innerOffset = BigInteger.ZERO,
                                        indexVars = ind
                                )
                            }
                        } else {
                            return null
                        }
                    }
                    is ValueQualifier.RootQualifier.RootStridePointer -> {
                        if(right is ValueQualifier.RootQualifier.RootStridePointer) {
                            return StridingQualifier.joinStridePaths(left, right) { a, p ->
                                a.copy(stridePath = p)
                            }
                        } else if(right is ValueQualifier.RootQualifier.RootFieldPointer) {
                            return StridingQualifier.joinStridingAndField(left, right)
                        } else if(right == null) {
                            /**
                             * Again, we lazily detect when to start tracking indices via [analysis.pta.abi.EncoderAnalysis.ValueQualifier.RootQualifier.RootFieldPointer]
                             * so we query the Array state to see if we are missing some information.
                             */
                            val offs = rightState.getOffsetFor(buffer, k) ?: return null
                            return StridingQualifier.joinStridingAndField(left, ValueQualifier.RootQualifier.RootFieldPointer(
                                offs.logicalOffset
                            ))
                        } else {
                            return null
                        }
                    }
                    is ValueQualifier.OffsetQualifier.DynamicStart -> {
                        if(right is ValueQualifier.RootQualifier.RootFieldPointer) {
                            return if(parentAnalysis.isDynamicStartConsistent(
                                            dynamicState = leftState,
                                            dynamicObject = left,
                                            rootState = rightState,
                                            rootOffset = right.offset
                                    )) {
                                left
                            } else {
                                null
                            }
                        } else if(right !is ValueQualifier.OffsetQualifier.DynamicStart) {
                            return null
                        }
                        if(left.path is Unresolved && right.path is SerializedPath.Resolved) {
                            return joinQualifier(
                                buffer, k, right, rightState, left, leftState, parentAnalysis
                            )
                        /**
                          If we have already encoded an object into the buffer, and then begin encoding a static array of
                          dynamic elements,  at the top of the loop we will have an unresolved path in one dynamic start
                          and a resolved path in the other. Much like in the isDynamicStartConsistent case where we would join
                          with a RootField pointer we simply check if the fields in the unresolved state are consistent
                          with the level of nesting we see in the resolved case, i.e., starting from the resolved dynamicstarts's object
                          root, will dereferencing the offset fields in the unresolved path yield the object path in the resolved dynamic
                          object?
                         */
                        } else if(left.path is SerializedPath.Resolved && right.path is Unresolved &&
                            parentAnalysis.getABILayoutOfType(left.path.o.root, rightState)?.derefFields(right.path.fields)?.path == left.path.o &&
                                leftState.encoderState.encoding?.varRoots?.get(right.path.root)?.objectPath?.contains(
                                    ObjectPathGen.Root(left.path.o.root)) == true) {
                            return left
                        }
                        /**
                         * When encoding a static array of dynamic objects, on the first iteration will we assume that
                         * the dynamic object representing the element of the static array lives at a constant field.
                         * After going back around the loop, we determine the path isn't a constant offset field,
                         * but rather a static array field. This allows "promotion" of the path in the first case by
                         * detecting when the paths inferred on the first iteration (i.e., at a constant field)
                         * are consistent with those assumed to be within a static array.
                         */
                        if(left.path != right.path && left.path is SerializedPath.Resolved && right.path is SerializedPath.Resolved) {
                            val weakJoin = left.path.o.joinOrNull(right.path.o) ?: return null
                            if(left.abiType == null || right.abiType == null) {
                                return null
                            }
                            /*
                              Equiv means that the structure of the types are the same
                             */
                            if(!left.abiType.equivModuloPath(right.abiType)) {
                                return null
                            }
                            val staticEquiv = if(weakJoin == left.path.o) {
                                left
                            } else if(weakJoin == right.path.o) {
                                right
                            } else {
                                return null
                            }
                            return staticEquiv.copy(
                                    lastWrittenOffset = left.lastWrittenOffset.takeIf {
                                        it == right.lastWrittenOffset
                                    },
                                    indexVars = left.indexVars.intersect(right.indexVars)
                            )
                        }
                        /**
                         * In every other case, we expect strict equality for joins
                         */
                        if(left.path != right.path) {
                            return null
                        }
                        if(left.abiType != null && right.abiType != null && left.abiType != right.abiType) {
                            return null
                        }
                        if(left.sort != null && right.sort != null && right.sort != left.sort) {
                            return null
                        }
                        ValueQualifier.OffsetQualifier.DynamicStart(
                                lastWrittenOffset = left.lastWrittenOffset.takeIf {
                                    it == right.lastWrittenOffset
                                },
                                path = left.path,
                                abiType = left.abiType.equalityJoin(right.abiType),
                                sort = left.sort.equalityJoin(right.sort),
                                indexVars = left.indexVars.intersect(right.indexVars)
                        )
                    }
                    is ValueQualifier.OffsetQualifier.ArrayElemStart -> {
                        if(right !is ElemPointer) {
                            return null
                        }
                        if(right == left) {
                            return left
                        }
                        if(left.parent != right.parent) {
                            return null
                        }
                        if(right is ValueQualifier.OffsetQualifier.ArrayElemStart) {
                            return left.copy(
                                    indexVar = right.indexVar.intersect(left.indexVar)
                            )
                        }
                        return ValueQualifier.OffsetQualifier.ArrayElem(
                                parent = right.parent,
                                indexVar = right.indexVar.intersect(left.indexVar)
                        )
                    }
                    is ValueQualifier.OffsetQualifier.ArrayElem -> {
                        if(right !is ElemPointer) {
                            return null
                        }
                        if(right == left) {
                            return left
                        }
                        if(left.parent != right.parent) {
                            return null
                        }
                        return left.copy(
                                indexVar = left.indexVar.intersect(right.indexVar)
                        )
                    }
                    /**
                     * Basic "strict-equality" join rules
                     */
                    is ValueQualifier.OffsetPointerFor -> {
                        if(right !is ValueQualifier.OffsetPointerFor || left.parent != right.parent) {
                            return null
                        }
                        return left
                    }
                    is ValueQualifier.OffsetForStart -> {
                        return left.takeIf { it == right }
                    }
                    is ValueQualifier.AddedBytesLength -> {
                        return if (right !is ValueQualifier.AddedBytesLength || !right.v.containsAny(right.v)) {
                            null
                        } else {
                            ValueQualifier.AddedBytesLength(
                                    left.v.intersect(right.v)
                            )
                        }
                    }
                    is ValueQualifier.ModuloBytesLength -> {
                        return if (right !is ValueQualifier.ModuloBytesLength || !right.v.containsAny(left.v)) {
                            null
                        } else {
                            ValueQualifier.ModuloBytesLength(
                                    left.v.intersect(right.v)
                            )
                        }
                    }
                    is ValueQualifier.CleanedValue -> return right.takeIf { it == left }
                }
            }



            private fun PointsToDomain.getOffsetFor(buffer: WritablePointer, k: TACSymbol.Var): BufferOffset? {
                val c = this.arrayState[k]?.let {
                    it as? ArrayStateAnalysis.Value.ElementPointer
                }?.takeIf {
                    it.arrayPtr.any {
                        this.pointsToState.store[it] == buffer
                    }
                }?.index ?: this.arrayState[k]?.let {
                    it as? ArrayStateAnalysis.Value.ScratchPointer
                }?.takeIf { buffer == ScratchPointer }?.index
                return c?.takeIf { it.isConstant }?.c?.let {
                    if(it.mod(EVM_WORD_SIZE) == DEFAULT_SIGHASH_SIZE) {
                        BufferOffset(logicalOffset = it - DEFAULT_SIGHASH_SIZE, hasSighashOffset = true)
                    } else {
                        BufferOffset(logicalOffset = it, hasSighashOffset = false)
                    }
                }
            }

        }

        init {
            ptaInvariant(nextPointer == null || currPointer == null) {
                "Inconsistent state: have $nextPointer and $currPointer are both non-null"
            }
        }

        fun expectNext(): EncodingState {
            return this.copy(
                    expectNext = true
            )
        }

        /**
         * Abstracts the many steps required for adding a constant value to a dynamic start:
         * 1. Checking size maximums (and perhaps computing a next pointer if necessary)
         * 2. Marking the dynamic parent as a struct if it is not already.
         */
        fun doFieldAdditionFor(lhs: TACSymbol.Var, dynParent: TACSymbol.Var, offs: BigInteger, curr: BigInteger, maxSize: BigInteger?, eqSize: (TACSymbol.Var) -> ValueQualifier.OffsetQualifier?) : EncodingState? {
            if(offs.mod(EVM_WORD_SIZE) != BigInteger.ZERO) {
                return null
            }
            val parentObj = this.qualifiers[dynParent]?.let { it as? ValueQualifier.OffsetQualifier.DynamicStart } ?: return run {
                logger.debug {
                    "Asked to add $offs to $curr for dynamic parent $dynParent, but it isn't a dynamic start: ${this.qualifiers[dynParent]}"
                }
                null
            }

            val newVal = (if(offs + curr == maxSize) {
                eqSize(dynParent)
            } else if(maxSize == null || offs + curr < maxSize) {
                ValueQualifier.OffsetQualifier.EncodedFieldPointer(parent = dynParent, offset = curr + offs, indexVars = setOf()) /* TODO: do we need indices here? */
            } else {
                logger.debug {
                    "$offs + $curr for $dynParent is greater than maxSize: $maxSize"
                }
                return null
            }) ?: return null
            return if(parentObj.sort == null) {
                logger.debug {
                    "Marking $parentObj @ $dynParent as struct"
                }
                this.copy(
                        qualifiers = this.qualifiers + (dynParent to parentObj.copy(sort = DynamicSort.STRUCT)) + (lhs to newVal)
                )
            } else {
                this.copy(
                        qualifiers = this.qualifiers + (lhs to newVal)
                )
            }
        }

        fun transitionNext(lhs: TACSymbol.Var): EncodingState {
            ptaInvariant(this.nextPointer == null) {
                "Attemping top mark $lhs as the next pointer, but we already have ${this.nextPointer}"
            }
            return this.copy(
                    nextPointer = lhs,
                    currPointer = null,
                    expectNext = false
            ).clearOffsetFor()
        }

        private fun clearOffsetFor() : EncodingState {
            val qual = this.qualifiers.retainAllValues { valueQualifier ->
                (valueQualifier !is ValueQualifier.OffsetForStart) && (valueQualifier !is ValueQualifier.OffsetPointerFor)
            }
            return this.copy(
                    qualifiers = qual,
                    lastRootWrite = null
            )
        }

        fun transitionCurr(lhs: TACSymbol.Var) : EncodingState {
            return this.copy(
                    currPointer = lhs,
                    nextPointer = null
            ).clearOffsetFor()
        }

        fun clearLastWrittenOffset(p: TACSymbol.Var) : EncodingState {
            return this.copy(
                    qualifiers = this.qualifiers.update(p) {
                        ptaInvariant(it is ValueQualifier.OffsetQualifier.DynamicStart) {
                            "Asked to clear the last rwritten offset for $p but it is not a dynamic start: $it"
                        }
                        it.copy(
                                lastWrittenOffset = null
                        )
                    } ?: throw AnalysisFailureException("Asked to clear last written offset of $p but it is not in qualifiers"),
                    expectNext = false
            )
        }

        fun kill(lhs: TACSymbol.Var): EncodingState {
            return this.copy(nextPointer = this.nextPointer?.takeIf { it != lhs },
                    currPointer = this.currPointer?.takeIf { it != lhs },
                    qualifiers = (this.qualifiers - lhs).updateValues { _, d ->
                        if(!d.references(lhs)) {
                            d
                        } else {
                            d.killOrNull(lhs)
                        }
                    },
                    varRoots = this.varRoots.retainAllValues { topLevelWrite ->
                        topLevelWrite.objectPath.none {
                            it.rootVar == lhs
                        }
                    },
                    lastRootWrite = lastRootWrite?.let {
                        it.copy(baseVariables = it.baseVariables - lhs)
                    }?.takeIf {
                        it.baseVariables.isNotEmpty() && it.symbol != lhs
                    }
            )
        }

        fun join(
            parentAnalysis: EncoderAnalysis,
            other: EncodingState,
            thisContext: PointsToDomain,
            otherContext: PointsToDomain
        ): EncodingState? {
            if(this.buffer != other.buffer || this.expectNext != other.expectNext) {
                return null
            }
            val quals = treapMapBuilderOf<TACSymbol.Var, ValueQualifier>()
            for(k in this.qualifiers.keys) {
                quals[k] = joinQualifier(
                        buffer = this.buffer,
                        k = k,
                        left = other.qualifiers[k],
                        leftState = otherContext,
                        right = this.qualifiers[k],
                        rightState = thisContext,
                        parentAnalysis = parentAnalysis
                ).also {
                    if(it == null) {
                      logger.info {
                          "Join of values @ $k: ${other.qualifiers[k]} and ${this.qualifiers[k]} yielded null"
                      }
                    }
                } ?: continue
            }
            /**
             * We can't skip the keys not in the intersection because of the case where we didn't (lazily) track root
             * field pointers.
             */
            for(k in other.qualifiers.keys) {
                if(k in this.qualifiers) {
                    continue
                }
                quals[k] = joinQualifier(
                        buffer = this.buffer,
                        k = k,
                        left = other.qualifiers[k],
                        leftState = otherContext,
                        right = null,
                        rightState = thisContext,
                        parentAnalysis = parentAnalysis
                ).also {
                    if(it == null) {
                        logger.info {
                            "Join of value @ $k ${other.qualifiers[k]} and null yielded null"
                        }
                    }
                } ?: continue
            }
            fun Map<TACSymbol.Var, ValueQualifier>.allSmaller(k: TACSymbol.Var) = this[k]?.let {
                it as? ValueQualifier.RootQualifier.RootFieldPointer
            }?.let {
                this.none { (_, v) ->
                    v is ValueQualifier.RootQualifier.RootFieldPointer && v.offset > it.offset
                }
            } == true || this[k]?.let {
                it as? ValueQualifier.OffsetQualifier.EncodedFieldPointer
            }?.let {
                this.none { (_, v) ->
                    v is ValueQualifier.OffsetQualifier.EncodedFieldPointer && v.parent == it.parent && v.offset > it.offset
                }
            } == true
            /**
             * Usually the next pointer has to be present (and equal) in both states. However, in some optimization cases,
             * at a join what is considered the "next" pointer in one branch that is actually at a root index in another branch.
             * If that root index is the largest extant root field pointer, then it is probably okay to consider that root index
             * a next pointer.
             *
             * Here is an example of where this might happen. When encoding uint[][3] to root index 0, solidity can compute:
             *
             * x = 32;
             * nxt = x + 96; // aka 32 * 3
             * it = x;
             * for(i = 0; i < 3; i++) {
             *    mem[it] = nxt - x;
             *    // encode the array at nxt...
             *    nxt = nxt + sizeOfEncodedArray;
             *    it += 32
             * }
             * when entering the loop for the first time, we will assume that nxt is just a regular old root field pointer.
             * However, within the loop it is meant to be the next pointer, where the next element of the static array is
             * encoded. After the first iteration, when computing nxt = nxt + sizeOfEncodedArray, the analysis will mark nxt
             * as the nextPointer. When joining at the top of the loop, we need exactly this heuristic to ensure that nxt
             * indeed serves the role of a next pointer.
             *
             * Note that we may have to do something similar with EncodedFieldPointer if multiple objects are being encoded,
             * `allSmaller` handles both cases
             */
            val nextPointer = if(this.nextPointer != null && other.nextPointer == null && other.qualifiers.allSmaller(this.nextPointer)) {
                this.nextPointer
            } else if(other.nextPointer != null && this.nextPointer == null && this.qualifiers.allSmaller(other.nextPointer)) {
                other.nextPointer
            } else {
                this.nextPointer.takeIf { it == other.nextPointer }
            }
            if(this.rootAlignment != other.rootAlignment) {
                logger.warn {
                    "Join of inconsistent root alignments: ${this.rootAlignment} vs ${other.rootAlignment}"
                }
                return null
            }
            return EncodingState(
                qualifiers = quals.build(),
                nextPointer = nextPointer,
                currPointer = other.currPointer.takeIf { it == this.currPointer },
                buffer = buffer,
                expectNext = this.expectNext,
                varRoots = this.varRoots.pointwiseMerge(other.varRoots) { v1, v2 ->
                    /*
                      If we've already determined a constant value at a root index is a dynamic offset
                      for some field, prefer that information over the constant info.
                     */
                    if((v1.isDefinitelyOffset && v1.objectPath.isNotEmpty()) && !v2.isDefinitelyOffset) {
                        // TODO: Check consistency (CERT-8094)
                        return@pointwiseMerge v1
                    } else if((v2.isDefinitelyOffset && v2.objectPath.isNotEmpty()) && !v1.isDefinitelyOffset) {
                        return@pointwiseMerge v2
                    }
                    if(v1.isDefinitelyOffset && v2.isDefinitelyOffset) {
                        if (v1.objectPath.isEmpty() && v1.isUnresolvedOffset && !v2.isUnresolvedOffset) {
                            return@pointwiseMerge v2
                        } else if(v2.objectPath.isEmpty() && v2.isUnresolvedOffset && !v1.isUnresolvedOffset) {
                            return@pointwiseMerge v1
                        }
                    }
                    val const = v1.const.equalityJoin(v2.const)
                    val paths = v1.objectPath.intersect(v2.objectPath)
                    /*
                      If this isn't a constant value, but we don't have any shared paths, something has gone wrong.
                     */
                    if(const == null && paths.isEmpty()) {
                        logger.info {
                            "Have that ${v1.const} is null, but $v1 and $v2 have no paths in common"
                        }
                        null
                    } else {
                        TopLevelWrite(
                            const = const,
                            objectPath = paths,
                            isDefinitelyOffset = v1.isDefinitelyOffset && v2.isDefinitelyOffset,
                            isUnresolvedOffset = v1.isUnresolvedOffset && v2.isUnresolvedOffset,
                        )
                    }
                },
                rootStrides = rootStrides.pointwiseMerge(other.rootStrides) { l, r -> l + r },
                expectNextWriteZero = this.expectNextWriteZero and other.expectNextWriteZero,
                lastRootWrite = this.lastRootWrite?.takeIf {
                    it == other.lastRootWrite
                },
                rootAlignment = this.rootAlignment,
                copyBuffers = copyBuffers.pointwiseMerge(other.copyBuffers) { a, b ->
                    if(a == b) {
                        a
                    } else {
                        null
                    }
                }
            )
        }
    }


    enum class DynamicSort {
        ARRAY,
        STRUCT
    }

    /**
     * As mentioned elsewhere, encoder routines may write seemingly unrelated values into locations of an encoded buffer,
     * where these values are actually offsets to a child dynamic object. However, we can't determine that these
     * values are offsets at the time of the write and have to wait to see the computation of the offset. Thus, we record
     * the written value (in [OffsetWrite]) and the location of the write (i.e., was it a field, or a static array elem)
     * together into the parent dynamic type. When we later see the value being used as an offset, we use the information
     * recorded in [OffsetLocation] to determine the path to the (newly computed) child object.
     */
    sealed class OffsetLocation {
        data class Field(val offset: BigInteger) : OffsetLocation()
        object Elem : OffsetLocation()
        object StaticArray : OffsetLocation()
    }

    /**
     * Records that we saw a (likely) offset write of value [offset] at [where] within some dynamic object
     * (recorded in [analysis.pta.abi.EncoderAnalysis.ValueQualifier.OffsetQualifier.DynamicStart.lastWrittenOffset])
     */
    data class OffsetWrite(val offset: TACSymbol, val where: OffsetLocation)

    sealed class ValueQualifier {
        abstract fun references(v: TACSymbol.Var) : Boolean
        abstract fun collectReferenced(m: MutableCollection<TACSymbol.Var>)
        open fun killOrNull(lhs: TACSymbol.Var) : ValueQualifier? = null
        sealed class OffsetQualifier : ValueQualifier() {

            /**
             * The beginning of a dynamic (according to the ABI specification) object. It assumed
             * that every dynamic object that is being encoded has exactly one corresponding
             * DynamicStart qualifier.
             *
             * The [path] of the object is resolved at the first write of an array length, and until then
             * it is represented by a [SerializedPath.Unresolved] object.
             *
             * The [sort] describes the shape of the object (array or struct) and can be resolved before the type
             * and path are resolved. [lastWrittenOffset] records the last offset-looking value that has been written
             * at some point into this object. (In some cases solidity will write the offset of a child
             * dynamic object before computing the next pointer. In such cases we need to remember the offset and then
             * at "next pointer" computation time immediately transition the next pointer directly to a child of the
             * relevant dynamic start).
             *
             * The [abiType] gives (coarse-grained) type information when the path of the object is resolved
             */
            data class DynamicStart(
                    val path: SerializedPath,
                    val sort: DynamicSort?,
                    val lastWrittenOffset: OffsetWrite?,
                    override val indexVars: Set<TACSymbol.Var>,
                    val abiType: LinearizedType?
            ) : OffsetQualifier(), WithIndexing<ValueQualifier> {
                override fun references(v: TACSymbol.Var): Boolean = lastWrittenOffset?.offset == v || (
                        path is SerializedPath.Resolved && path.o.rootVar == v
                    )

                override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {
                    if(path is SerializedPath.Resolved) {
                        path.o.root.let {
                            it as? ObjectPathAnalysis.ObjectRoot.V
                        }?.v?.let(m::add)
                    }
                    if(lastWrittenOffset != null && lastWrittenOffset.offset is TACSymbol.Var) {
                        m.add(lastWrittenOffset.offset)
                    }
                    m.addAll(indexVars)
                }

                init {
                    check(sort == null || abiType == null ||
                            (abiType is LinearizedType.Struct && sort == DynamicSort.STRUCT) ||
                            ((abiType is LinearizedType.Array || abiType is LinearizedType.EmptyArray) && sort == DynamicSort.ARRAY)) {
                        "Sort $sort $abiType"
                    }
                }

                override val constIndex: BigInteger?
                    get() = BigInteger.ZERO.takeIf {
                        this.sort != DynamicSort.ARRAY
                    }
                override val untilEndVars: Set<TACSymbol.Var>
                    get() = setOf()

                override fun withVars(addIndex: Iterable<TACSymbol.Var>, addUntilEnd: Iterable<TACSymbol.Var>): ValueQualifier = this.copy(
                        indexVars = this.indexVars + addIndex
                )
            }

            /**
             * A pointer which "strides" over specific intervals. When encoding statically sized arrays the code
             * generated by the solidity compiler will use (constant) loops that increment an output pointer (the DynamicStridePointer)
             * by the *size* of the static array elements. For a simple case such as `uint[3]`, the serialization code
             * will begin at the first element of the static array, and then iterate three times, incrementing the output pointer
             * by 32 on each iteration. The DSP is an abstract summary of this behavior, summarizing the *possible*
             * locations visited by the pointer during iteration (see below for how).
             *
             * Note that with nested, non-dynamic statically sized arrays the striding behavior is more complex. Static
             * types are flattened, and thus a type like `uint[3][5][6]` will be flattened to 3*5*6 = 90 contiguous words
             * when being serialized. Solidity generates three nested loops. The outermost loop iterates 6 times, and at
             * each iteration increments its output location by 3*5*32 = 480 bytes. The next loop iterates 5 times, and
             * increments (a copy of) the outer loop's pointer by 3 * 32 = 96 bytes. Finally, the innermost loop
             * interates 3 times, and increments (a copy of) the middle loop's pointer by 32.
             *
             * Each of the pointers in these loops is associated with a DSP which describes the set of possible locations
             * touched by the loop. The details are below, but roughly: the outer loop's DSP captures that it begins
             * at some point and iterates 480 bytes at a time; the middle loop captures that it iterates in 96 byte
             * chunks STARTING FROM some point that must be 480 byte aligned; and the inner loop captures that it
             * iterates in 32 byte chunks, starting from a point that is 96 bytes aligned within some point that is itself
             * 480 byte aligned. In other words, the inner loop's DSP captures that the pointer touches any location
             * reachable by: iterating in 480 byte chunks some number of times, then iterating in 96 byte chunks some number
             * of times, and finally iterating by 32 bytes some number of times.
             *
             * The actual striding behavior above is given by the [StridePath] object, the [strideBy] and [innerOffset] fields.
             * The [strideBy] field describes the "inner most" stride; in the inner loop example above, this would
             * be 32. The [stridePath] field describes any striding that "prefixes" the striding described in [strideBy].
             * In the inner loop example above, this would be a representation (rougly) of [480, 96], i.e. the striding
             * of [strideBy] begins from a point reached by striding 480 bytes at a time, then 96 bytes at a time.
             * Note that the [StridePath] type also includes the "root offset" (i.e., the offset from the dynamic parent
             * [parent] at which the striding begins) and can also includes "constant offsets".
             *
             * The [innerOffset] field captures offsets within a striding pointer. If the component type
             * of the statically sized array is static and of complex type (i.e., a struct) we need to describe
             * locations that are offset from a striding pointer. For example, suppose we are encoding the type
             * `A[3]` where A is a struct with two uint fields, `f1` and `f2`. Then the variable used to write
             * the `f2` field will have [innerOffset] 32, and the the strideBy will be 64.
             */
            data class DynamicStridePointer(
                    val parent: TACSymbol.Var,
                    override val stridePath: StridePath,
                    override val strideBy: BigInteger,
                    override val innerOffset: BigInteger,
                    override val indexVars: Set<TACSymbol.Var>
            ) : OffsetQualifier(), StrideWithIndexing {
                override fun references(v: TACSymbol.Var): Boolean {
                    return this.parent == v || v in indexVars
                }

                override fun killOrNull(lhs: TACSymbol.Var): ValueQualifier? {
                    if(parent != lhs && lhs in indexVars) {
                        return this.copy(
                                indexVars = this.indexVars - lhs
                        )
                    } else {
                        return null
                    }
                }


                override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {
                    m.add(parent)
                    m.addAll(indexVars)
                }

                override val constIndex: BigInteger?
                    get() = null
                override val untilEndVars: Set<TACSymbol.Var>
                    get() = setOf()

                override fun withVars(addIndex: Iterable<TACSymbol.Var>, addUntilEnd: Iterable<TACSymbol.Var>): DynamicStridePointer {
                    return this.copy(
                            indexVars = this.indexVars + addIndex
                    )
                }
            }

            /**
             * The beginning of the array data segment for a dynamic object in [parent] that is known to be an array.
             * The [indexVar] field will be all variables provably known to be 0.
             */
            data class ArrayElemStart(override val parent: TACSymbol.Var, override val indexVar: Set<TACSymbol.Var>) : OffsetQualifier(), ElemPointer {
                override fun references(v: TACSymbol.Var): Boolean = v == parent || indexVar.contains(v)
                override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {
                    m.add(parent)
                }
            }

            /**
             * Some array element of the dynamic array object at [parent]. The [indexVar] are the set of variables
             * that give the (logical) index of the element.
             */
            data class ArrayElem(override val parent: TACSymbol.Var, override val indexVar: Set<TACSymbol.Var>) : OffsetQualifier(), ElemPointer {
                override fun references(v: TACSymbol.Var): Boolean = parent == v || v in indexVar
                override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {
                    m.add(parent)
                }
            }

            /**
             * A field of some encoded object. [parent] could be an [ArrayElem] or [ArrayElemStart] (in which case
             * the array component MUST be a non-dynamic struct type) or a [DynamicStart] in which case
             * the parent type must be a struct type (potentially dynamic).
             *
             * Note that fields of structs encoded within static arrays are abstracted using the [DynamicStridePointer]
             * as described above.
             */
            data class EncodedFieldPointer(
                    val parent: TACSymbol.Var,
                    override val offset: BigInteger,
                    override val indexVars: Set<TACSymbol.Var>
            ) : OffsetQualifier(), WithIndexing<ValueQualifier>, FieldPointer {
                override fun references(v: TACSymbol.Var): Boolean = parent == v
                override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {
                    m.add(parent)
                }

                override val constIndex: BigInteger
                    get() = offset
                override val untilEndVars: Set<TACSymbol.Var>
                    get() = setOf()

                override fun withVars(addIndex: Iterable<TACSymbol.Var>, addUntilEnd: Iterable<TACSymbol.Var>): ValueQualifier {
                    return this.copy(
                            indexVars = this.indexVars + addIndex
                    )
                }
            }

        }

        /**
         * The [OffsetQualifier] class above abstracted locations at some (non-constant)
         * index in the buffer. In contrast [RootQualifier] objects all have constant (-ish in the case
         * of the RootStridePointer) indices within the encoded buffer.
         */
        sealed class RootQualifier : ValueQualifier() {
            /**
             * The "constant" version of the [OffsetQualifier.DynamicStridePointer]. Unlike the [OffsetQualifier.DynamicStridePointer], which
             * begins at some offset relative to a dynamic object, the [RootStridePointer] begins at some constant index
             * within the encoded buffer. The meaning of [stridePath], [strideBy] and [innerOffset] are all
             * the same as in the [OffsetQualifier.DynamicStridePointer] case.
             */
            data class RootStridePointer(
                    override val stridePath: StridePath,
                    override val strideBy: BigInteger,
                    override val innerOffset: BigInteger,
                    override val indexVars: Set<TACSymbol.Var>
            ) : RootQualifier(), StrideWithIndexing {
                override fun killOrNull(lhs: TACSymbol.Var): ValueQualifier? {
                    if(lhs in indexVars) {
                        return this.copy(
                                indexVars = this.indexVars - lhs
                        )
                    } else {
                        return null
                    }
                }

                override val constIndex: BigInteger?
                    get() = null
                override val untilEndVars: Set<TACSymbol.Var>
                    get() = setOf()

                override fun withVars(addIndex: Iterable<TACSymbol.Var>, addUntilEnd: Iterable<TACSymbol.Var>): RootStridePointer {
                    return this.copy(
                            indexVars = this.indexVars + addIndex
                    )
                }

                override fun references(v: TACSymbol.Var): Boolean {
                    return v in indexVars
                }

                override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {
                    m.addAll(indexVars)
                }
            }

            /**
             * A constant index within the encoded buffer.
             */
            data class RootFieldPointer(override val offset: BigInteger) : RootQualifier(), FieldPointer {
                override fun references(v: TACSymbol.Var): Boolean = false
                override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {

                }
            }
        }

        /**
         * An abstraction of the offset from a dynamic start of an object to the beginning of a child dynamic object.
         * Note that the dynamic start is not the same thing as the location of the dynamic object itself:
         * it is for structs, but for arrays it is the ArrayElemStart :(
         */
        data class OffsetPointerFor(val parent: TACSymbol.Var) : ValueQualifier() {
            override fun references(v: TACSymbol.Var): Boolean {
                return v == this.parent
            }

            override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {
                m.add(parent)
            }
        }

        /**
         * An abstraction of the offset from the root of the buffer to a top-level dynamic object. When
         * encoding call data, this is the offset of the dynamic object within the buffer minus 4, otherwise
         * it is the offset itself.
         */
        object OffsetForStart : ValueQualifier() {
            override fun references(v: TACSymbol.Var): Boolean = false
            override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {

            }
        }
        data class AddedBytesLength(val v: Set<TACSymbol.Var>) : ValueQualifier() {
            override fun references(v: TACSymbol.Var): Boolean = v in this.v
            override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {
                m.addAll(v)
            }
        }
        data class ModuloBytesLength(val v: Set<TACSymbol.Var>) : ValueQualifier() {
            override fun references(v: TACSymbol.Var): Boolean = v in this.v
            override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {
                m.addAll(v)
            }
        }

        /**
         *  A value that has been cleaned by the application of a bit mask that clears a contiguous range
         *  of most significant bits, i.e., the mask preserves a contiguous range of bits, starting from the least significant
         *  bit.
         */
        data class CleanedValue(val cleaned: TACSymbol.Var) : ValueQualifier() {
            override fun references(v: TACSymbol.Var): Boolean = v == this.cleaned
            override fun collectReferenced(m: MutableCollection<TACSymbol.Var>) {
                m.add(this.cleaned)
            }
        }
    }


    interface ElemPointer {
        val parent: TACSymbol.Var
        val indexVar: Set<TACSymbol.Var>
    }

    /**
     * A uniform representation of dynamic objects. [dyn] is the [ValueQualifier.OffsetQualifier.DynamicStart]
     * being abstracted, [dynVar] is the variable that has [dyn] as its abstract value, and [addBase] is the
     * variable against which child offsets are computed (i.e., when computing the offset for a child dynamic object,
     * the value of [addBase] is subtracted from the offset of the child [ValueQualifier.OffsetQualifier.DynamicStart]).
     * As noted above, [dyn] and [addBase] are different for arrays.
     */
    private data class DynamicObject(
            val dyn: ValueQualifier.OffsetQualifier.DynamicStart,
            val dynVar: TACSymbol.Var,
            val addBase: TACSymbol.Var
    )

    private val semantics = object : AbstractExpressionCaseInterpreter<EncodingState, Pair<State, PointsToDomain>>() {
        override fun forget(lhs: TACSymbol.Var, toStep: EncodingState, input: EncodingState, whole: Pair<State, PointsToDomain>, wrapped: LTACCmd): EncodingState {
            return toStep.kill(lhs)
        }

        override fun stepAssignAdd(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: EncodingState,
            input: EncodingState,
            whole: Pair<State, PointsToDomain>,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): EncodingState {
            return (if(o1 !is TACSymbol.Var) {
                if(o2 !is TACSymbol.Var) {
                   super.stepAssignAdd(lhs, o1, o2, toStep, input, whole, l)
                } else {
                    internalAdd(o1 = o2, o2 = o1, input = input, toStep = toStep, l = l, lhs = lhs, wholePacked = whole)
                }
            } else if(o1 !in toStep.qualifiers && o2 is TACSymbol.Var && o2 in toStep.qualifiers) {
                internalAdd(o1 = o2, o2 = o1, input = input, toStep = toStep, l = l, lhs = lhs,  wholePacked = whole)
            } else {
                internalAdd(o1 = o1, o2 = o2, input = input, toStep = toStep, l = l, lhs = lhs,  wholePacked = whole)
            }) ?: super.stepAssignAdd(lhs, o1, o2, toStep, input, whole, l)
        }

        private fun internalAdd(
            o1: TACSymbol.Var,
            o2: TACSymbol,
            lhs: TACSymbol.Var,
            toStep: EncodingState,
            input: EncodingState,
            wholePacked: Pair<State, PointsToDomain>,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): EncodingState? {
            val q1 = toStep.qualifiers[o1]
            val q2 = toStep.qualifiers[o2]
            val dynStart = extractBase(o1, toStep)
            val whole = wholePacked.second
            val constO2 = numeric.interpAsConstant(whole, l.wrapped, o2)
            check(o1 != toStep.currPointer || q1 is ValueQualifier.OffsetQualifier.DynamicStart) {
                "Have that $o1 is the current pointer but is not a dynamic start: $q1"
            }
            /*
                Compute the linear terms generated by this addition
             */
            val invariants by lazy {
                LinearInvariantSemantics.statementInterpreter.stepCommand(
                    l = l.wrapped,
                    whole = null,
                    input = whole.invariants,
                    toStep = whole.invariants.kill(l.cmd.lhs)
                )
            }
            /**
             * Are we adding some value to the current (i.e., mostly recently encoded) dynamic object?
             * If so, it is likely we are computing the next pointer. There is a whole bunch of checks
             * this entails...
             */
            if(dynStart != null && dynStart.dynVar == toStep.currPointer && toStep.nextPointer == null) {
                ptaInvariant(q1 is ValueQualifier.OffsetQualifier) {
                    "$q1 ($o1) is supposed to be an OffsetQualifier?"
                }
                /**
                 * First check: is this addition computing the offset for a new root? When could this *possibly* happen?
                 * Well dear reader, consider encoding an array a followed by another dynamic type:
                 *
                 * buffer[0] := 64;
                 * buffer[64] := a.length;
                 * start := 96;
                 * // copy a starting buffer[96]
                 * sz := a.length * 32;
                 * r1 := 96 + sz;
                 * buffer[32] = r1; // r1 is recorded as the lastRootWrite, at logicalindex 32
                 * nxt := r1 + start // nxt is now the offset of the dynamic start for the second dynamic object being encoded
                 *
                 * Transposing the above example to our code below, lhs is nxt, lastRootWrite.symbol is r1 and baseVariables
                 * are the set of variables that point to buffer[0] (buffer[0] here is shorthand for "a write to a pointer
                 * that points to logical index 0 in the buffer").
                 */
                if (toStep.lastRootWrite != null && invariants.mapNotNull {
                        it.definingIntEquationFor(toStep.lastRootWrite.symbol)?.let(LinearTerm.Companion::lift)
                    }.let { terms ->
                        toStep.lastRootWrite.baseVariables.any {
                            terms.any { t ->
                                invariants implies {
                                    !lhs `=` !it + t
                                }
                            }

                        }
                    }) {
                    return toStep.copy(
                        qualifiers = toStep.qualifiers + (lhs to ValueQualifier.OffsetQualifier.DynamicStart(
                            path = Unresolved( // all we know is that this is a dynamic object that is rooted at the logical field
                                root = toStep.lastRootWrite.logicalField,
                                fields = listOf()
                            ),
                            sort = null,
                            indexVars = setOf(),
                            lastWrittenOffset = null,
                            abiType = null
                        )),
                        varRoots = toStep.varRoots + (toStep.lastRootWrite.logicalField to
                                TopLevelWrite(
                                    isDefinitelyOffset = true,
                                    objectPath = setOf(),
                                    const = null,
                                    isUnresolvedOffset = true
                                )
                            )
                    ).transitionCurr(lhs) // lhs is definitely the most recent dynamic start pointer
                }
                // TODO(jtoman): bounds checking something something
                val knownOffsets = toStep.qualifiers.mapNotNull { (k, v) ->
                    if (v !is ValueQualifier.OffsetQualifier.DynamicStart) {
                        return@mapNotNull null
                    }
                    val dynObject = extractBase(k, toStep) ?: return@mapNotNull null
                    if (dynObject.dyn.lastWrittenOffset == null) {
                        return@mapNotNull null
                    }
                    /**
                     * Same story as above, but is the result of this addition equal to adding some offset written
                     * in some dynamic object to the beginning of that object? if so, transition immediately to
                     * a new dynamic start, with lhs as the current object (handled by [matchAdditionToWrite])
                     */
                    matchAdditionToWrite(
                        inv = invariants,
                        m = input,
                        nextPointer = lhs,
                        dyn = dynObject,
                        writeValue = dynObject.dyn.lastWrittenOffset.offset,
                        writeLoc = dynObject.dyn.lastWrittenOffset.where
                    )?.clearLastWrittenOffset(dynObject.dynVar)
                }
                if (knownOffsets.size == 1 && isSafeBoundFor(o1, o2, toStep)) {
                    return knownOffsets.first()
                /*
                   Check if we are now computing the *end* of the current block, in this case, update the next pointer

                   Here: Are we adding the length of the array times the the size of each element to the addBase (aka
                   ElementStart). If so, then the result is the next pointer.
                 */
                } else if (dynStart.dyn.sort == DynamicSort.ARRAY && dynStart.dyn.path is SerializedPath.Resolved &&
                    dynStart.dyn.abiType?.let { it as? LinearizedType.Array }?.takeIf {
                        !it.isByte
                    }?.cont?.sizeInArray?.let {
                        val candidateLen = lengthVarsForEncodedArray(dynStart.dyn, whole).orEmpty()
                        candidateLen.any { k ->
                            invariants implies {
                                !lhs `=` !k * it + !dynStart.addBase
                            }
                        }
                    } == true
                ) {
                    return toStep.transitionNext(lhs)
                /*
                   What if we encode an empty array!?!? HAHAHA SO GLAD YOU ASKED. Let's go step by step...
                 */
                } else if (dynStart.dyn.sort == DynamicSort.ARRAY && dynStart.dyn.path is SerializedPath.Resolved &&
                    dynStart.dyn.abiType?.let { it as? LinearizedType.EmptyArray }?.let {
                        whole.objectPath.any { (k, v) ->
                            /*
                               Find variables that are the length of the empty array being encoded...
                             */
                            ObjectPathGen.ArrayLength(dynStart.dyn.path.o) in v &&
                                    // that must equal zero...
                                    whole.boundsAnalysis[k]?.let {
                                        it as? QualifiedInt
                                    }?.x?.takeIf { it.isConstant }?.c == BigInteger.ZERO &&
                                    /*
                                       find the coefficients applied to this variable
                                     */
                                    invariants.mapNotNull {
                                        it.term[LVar.PVar(k)]?.abs()
                                    }.toSet().any {
                                        /* apply this coefficient to k and see if it matches the expected format for computing the end
                                           of the array.
                                           TODO(jtoman): isn't this equivalent to doing propagateConst(k, 0).implies { !lhs `=` !dynStart.addBase }???
                                         */
                                        invariants implies {
                                            !lhs `=` !k * it + !dynStart.addBase
                                        }
                                    }
                        }
                    } == true
                ) {
                    return toStep.transitionNext(lhs)
                /*
                 * Are we adding the length of the array rounded up to the nearest 32 bytes to the base of this array? If so, this is also the end
                 */
                } else if (q2 is ValueQualifier.ModuloBytesLength &&
                    (dynStart.dyn.abiType?.let { it as? LinearizedType.Array }?.isByte == true ||
                            dynStart.dyn.abiType is LinearizedType.EmptyArray) &&
                    invariants implies {
                        !lhs `=` !dynStart.addBase + !o2
                    } && dynStart.dyn.path is SerializedPath.Resolved &&
                    q2.v.any { objectArray ->
                        getArrayInfo(objectArray, whole).paths?.contains(dynStart.dyn.path.o) ?: false
                    }
                ) {
                    return toStep.transitionNext(lhs)
                    /*
                   If we are adding to a struct, and the result is the size of the struct
                 */
                } else if (dynStart.dyn.abiType is LinearizedType.Struct && invariants implies {
                        !lhs `=` !dynStart.addBase + (dynStart.dyn.abiType.offset.size.toBigInteger() * EVM_WORD_SIZE)
                    }) {
                    return toStep.transitionNext(lhs)
                }
            } // end next pointer computation from currPointer
            else if(toStep.nextPointer != null && invariants implies {
                    !lhs `=` !toStep.nextPointer
                }) {
                // weird, we are recomputing the next pointer again?
                return toStep.kill(toStep.nextPointer).copy(nextPointer = lhs) // kill the current next pointer
            }
            if(q1 is ValueQualifier.OffsetQualifier.DynamicStart && q1.sort == DynamicSort.ARRAY && constO2 == EVM_WORD_SIZE) {
                return toStep.copy(
                        qualifiers = toStep.qualifiers + (lhs to ValueQualifier.OffsetQualifier.ArrayElemStart(
                                parent = o1,
                                indexVar = whole.variablesEqualTo(BigInteger.ZERO)
                        ))
                )
            } else if(q1 is ValueQualifier.OffsetQualifier.DynamicStart) {
                if(constO2 == null || q1.sort == DynamicSort.ARRAY) {
                    return null.andInfo {
                        "Addition of non-constant $q2 ($o2) @ $l to array dynamic start $q1 ($o1), failing"
                    }
                }
                // compute the field pointer as a result of adding a constant to a struct dynamic start.
                return toStep.doFieldAdditionFor(lhs = lhs, dynParent = o1, curr = BigInteger.ZERO, offs = constO2, maxSize = q1.abiType?.let {
                    check(it is LinearizedType.Struct)
                    it
                }?.totalEncodedSize()) { _ ->
                    /* unlike a struct within an array, adding
                        a value such that the result would be at exactly maxSize doesn't
                        yield anything element, it is just an error */
                    null
                }
            } else if(q1 is ValueQualifier.OffsetQualifier.EncodedFieldPointer) {
                val parentObj = toStep.qualifiers[q1.parent]?.let {
                    it as? ValueQualifier.OffsetQualifier.DynamicStart
                } ?: return null.andInfo {
                    "Could not find dynamic start for parent of $q1 ($o1) @ $l"
                }
                if(constO2 == null) {
                    return null.andInfo {
                        "Addining non-constant $q2 ($o2) to encoded field pointer $q1 ($o1) @ $l"
                    }
                }
                if(parentObj.sort == DynamicSort.ARRAY) {
                    ptaInvariant(parentObj.abiType != null && parentObj.abiType is LinearizedType.Array) {
                        "Have a dynamic sort of array, but do not have a type $parentObj @ $l"
                    }
                    /*
                      An encoded field pointer should *never* occur for a dynamic element type: there are no offsets!
                     */
                    ptaInvariant(!parentObj.abiType.cont.isDynamic) {
                        "Have field offset for array $parentObj with dynamic contents @ $l"
                    }
                    /*
                       Similarly, we must have multiple fields within each element
                     */
                    ptaInvariant(parentObj.abiType.cont is LinearizedType.Struct) {
                        "Have a field offset within an array $parentObj that is not a struct @ $l"
                    }
                    return toStep.doFieldAdditionFor(
                            lhs = lhs,
                            dynParent = q1.parent,
                            maxSize = parentObj.abiType.cont.sizeInArray,
                            offs = constO2,
                            curr = q1.offset
                    ) { _ ->
                        /*
                           If we have an array of structs with two fields, and then add 32 to a field pointer at offset 32
                           within an array element, the result is not going out of bounds, but another array element.

                           (This kind of assumes that we never go past the end of the array...)
                         */
                        ValueQualifier.OffsetQualifier.ArrayElem(parent = q1.parent, indexVar = setOf())
                    }
                } else {
                    ptaInvariant(parentObj.abiType == null || parentObj.abiType is LinearizedType.Struct) {
                        "Mismatched sort and type, has a sort ${parentObj.sort} but a type of ${parentObj.sort}"
                    }
                    ptaInvariant(parentObj.sort == null || parentObj.sort == DynamicSort.STRUCT) {
                        "Actually impossible: sort was not an array but isn't null or a struct: ${parentObj.sort}"
                    }
                    /**
                     * If we have a struct field with a dynamic object, the pointer simplifier/optimizer may yield:
                     * ```
                     * mem[p] = c + k // p:EncodedFieldPointer(parent, c)
                     * nxt = p + c + k
                     * ```
                     * nxt here is *not* another encoded field pointer, is the next pointer whose offset (c + k) was just
                     * written. This won't be recognized in the next pointer computation block above, so we special case it here.
                     */
                    if(q1.parent == toStep.currPointer && parentObj.lastWrittenOffset != null && toStep.expectNext) {
                        val stepped = matchAdditionToWrite(
                            inv = invariants,
                            dyn = extractBase(q1.parent, toStep)!!,
                            writeLoc = parentObj.lastWrittenOffset.where,
                            m = toStep,
                            nextPointer = lhs,
                            writeValue = parentObj.lastWrittenOffset.offset
                        )?.clearLastWrittenOffset(q1.parent)
                        if(stepped != null) {
                            return stepped
                        }
                    }
                    val maxSize = parentObj.abiType?.let { it as? LinearizedType.Struct }?.offset?.size?.toBigInteger()?.times(EVM_WORD_SIZE)
                    return toStep.doFieldAdditionFor(
                            lhs = lhs,
                            dynParent = q1.parent,
                            maxSize = maxSize,
                            offs = constO2,
                            curr = q1.offset
                    ) { _ -> null }
                }
            } else if(q1 is ElemPointer) {
                val parentArray = getParentArray(toStep, q1) ?: return null.andInfo {
                    "Could not find parent array of element $q1 ($o1) @ $l"
                }
                if(parentArray.abiType is LinearizedType.EmptyArray) {
                    /*
                      Literally no pointer operations except trivial ones are allowed on the encoding of empty arrays
                      (they are empty, there is no data!)
                     */
                    if(constO2 != BigInteger.ZERO || q1 !is ValueQualifier.OffsetQualifier.ArrayElemStart) {
                        return null.andInfo {
                            "Trying to compute element offsets in a provably empty array $parentArray @ $l"
                        }
                    }
                    return toStep.copy(
                            qualifiers = toStep.qualifiers + (lhs to q1)
                    )
                }
                ptaInvariant(parentArray.abiType is LinearizedType.Array) {
                    "Adding to $o1 (an elem pointer $q1) whose parent $parentArray has not been resolved to an array type"
                }
                ptaInvariant(parentArray.sort == DynamicSort.ARRAY) {
                    "Inconsistent sort and type for parent of $q1 ($o1): $parentArray"
                }
                if (constO2 == null) {
                    return null.andInfo {
                        "Adding a non-constant $q2 ($o2) to an element point $q1 ($o1) @ $l"
                    }
                }
                /*
                   If the content type is dynamic, the size in array must be 32, in which case this function will fail
                   except in the case where constO2 == 32, in which case it will produce ArrayElem.

                   If the content type is linear struct with a single non-dynamic field, this will again only produce ArrayElem
                   (or fail)

                   Otherwise, if maxSize is not 32 we must have a struct
                 */
                ptaInvariant(parentArray.abiType is LinearizedType.EmptyArray ||
                        parentArray.abiType.cont.sizeInArray == EVM_WORD_SIZE ||
                        parentArray.abiType.cont is LinearizedType.Struct) {
                    "The content type of $o1's parent array ${parentArray.abiType.cont} reports a non-word size of ${parentArray.abiType.cont.sizeInArray} but isn't a struct"
                }
                return toStep.doFieldAdditionFor(
                        lhs = lhs,
                        curr = BigInteger.ZERO,
                        offs = constO2,
                        maxSize = parentArray.abiType.cont.sizeInArray,
                        dynParent = q1.parent
                ) {
                    ValueQualifier.OffsetQualifier.ArrayElem(parent = it, indexVar = setOf())
                }
            } else if(q1 is ValueQualifier.OffsetQualifier.DynamicStridePointer && constO2 != null && constO2.mod(EVM_WORD_SIZE) == BigInteger.ZERO) {
                /*
                  Reset the stride
                 */
                return if (q1.innerOffset + constO2 == q1.strideBy) {
                    toStep.copy(
                            qualifiers = toStep.qualifiers + (l.cmd.lhs to q1.copy(
                                    innerOffset = BigInteger.ZERO
                            )))
                /* In principle this could be just another outer stride, with a new inner offset of (q.innerOffset + constO2).mod(q1.strideBy)
                   But that seems so unlikely that we just die here */
                } else if (q1.innerOffset + constO2 > q1.strideBy) {
                    null.andInfo {
                        "Stride $q1 ($o1) + $constO2 ($o2) exceeds stride size @ $l"
                    }
                } else {
                    toStep.copy(
                            qualifiers = toStep.qualifiers + (l.cmd.lhs to q1.copy(
                                    innerOffset = q1.innerOffset + constO2
                            )))
                }
            } else if(q1 is ValueQualifier.RootQualifier.RootFieldPointer && constO2 != null && constO2.mod(EVM_WORD_SIZE) == BigInteger.ZERO) {
                val newPhysicalIndex = whole.arrayState[o1]?.let {
                    it as? ArrayStateAnalysis.Value.IndexedElement
                }?.index?.takeIf { it.isConstant }?.c?.let {
                    it + constO2
                }?.takeIf {
                    it != BigInteger.ZERO
                }
                return toStep.copy(
                        qualifiers = toStep.qualifiers + (l.cmd.lhs to ValueQualifier.RootQualifier.RootFieldPointer(
                                offset = q1.offset + constO2
                        ))
                ).letIf(newPhysicalIndex != null) {
                    it.resolveAlignment(newPhysicalIndex!!.mod(EVM_WORD_SIZE))
                }
            } else if(q1 is ValueQualifier.RootQualifier.RootStridePointer && constO2 != null && constO2.mod(EVM_WORD_SIZE) == BigInteger.ZERO) {
                /*
                  Exactly the same rules as the DynamicStridePointer case
                 */
                if(q1.innerOffset + constO2 == q1.strideBy) {
                    return toStep.copy(
                            qualifiers = toStep.qualifiers + (l.cmd.lhs to q1.copy(
                                    innerOffset = BigInteger.ZERO
                            ))
                    )
                } else if(q1.innerOffset + constO2 > q1.strideBy) {
                    return null.andInfo {
                        "Stride $q1 ($o1) + $constO2 ($o2) exceeds stride size @ $l"
                    }
                } else {
                    return toStep.copy(
                            qualifiers = toStep.qualifiers + (l.cmd.lhs to q1.copy(
                                    innerOffset = q1.innerOffset + constO2
                            ))
                    )
                }
            } else if(constO2 == 0x1f.toBigInteger()) {
                val lengths = whole.boundsAnalysis[o1]?.let {
                    it as? QualifiedInt
                }?.qual?.asSequence()?.mapNotNull {
                    if(it is IntQualifier.LengthOfCalldataArray && getArrayInfo(it.calldataArrayVar, whole).elemMemorySize?.consistentWith(BigInteger.ONE) == true) {
                        it.calldataArrayVar
                    } else if(it is IntQualifier.LengthOfArray && getArrayInfo(it.arrayVar, whole).elemMemorySize?.consistentWith(BigInteger.ONE) == true) {
                        it.arrayVar
                    } else {
                        null
                    }
                }?.filter {
                    it != l.cmd.lhs
                }?.toSet()
                return if(lengths != null) {
                    toStep.copy(
                            qualifiers = toStep.qualifiers + (l.cmd.lhs to ValueQualifier.AddedBytesLength(lengths))
                    )
                } else {
                    null
                }
            }
            return null
        }

        private val clearLowerBits = MAX_EVM_UINT256.andNot(0x1f.toBigInteger())

        override fun stepAssignBWAnd(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: EncodingState,
            input: EncodingState,
            whole: Pair<State, PointsToDomain>,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): EncodingState {
            val o1Const = numeric.interpAsUnambiguousConstant(whole.second, ltacCmd = l.wrapped, value = o1)
            val o2Const = numeric.interpAsUnambiguousConstant(whole.second, ltacCmd = l.wrapped, value = o2)
            val d = if(o1Const == clearLowerBits) {
                toStep.qualifiers[o2]?.let {
                    it as? ValueQualifier.AddedBytesLength
                } ?: return toStep
            } else if(o2Const == clearLowerBits) {
                toStep.qualifiers[o1]?.let {
                    it as? ValueQualifier.AddedBytesLength
                } ?: return toStep
            } else if(o1Const?.plus(BigInteger.ONE)?.bitCount() == 1 && o2 is TACSymbol.Var) {
                return toStep.copy(
                    qualifiers = toStep.qualifiers + (l.cmd.lhs to ValueQualifier.CleanedValue(o2))
                )
            } else if(o2Const?.plus(BigInteger.ONE)?.bitCount() == 1 && o1 is TACSymbol.Var) {
                return toStep.copy(
                    qualifiers = toStep.qualifiers + (l.cmd.lhs to ValueQualifier.CleanedValue(o1))
                )
            } else {
                return toStep
            }
            return toStep.copy(
                qualifiers = toStep.qualifiers + (l.cmd.lhs to ValueQualifier.ModuloBytesLength(
                        d.v
                )))
        }

        override fun stepAssignVar(lhs: TACSymbol.Var, s: TACSymbol.Var, toStep: EncodingState, input: EncodingState, whole: Pair<State, PointsToDomain>, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): EncodingState {
            return if(toStep.qualifiers[s] is ValueQualifier.OffsetQualifier.DynamicStart) {
                if(lhs == s) {
                    return toStep
                } else if((toStep.qualifiers[s] as ValueQualifier.OffsetQualifier.DynamicStart).sort == DynamicSort.ARRAY) {
                    return toStep
                } else {
                    /*
                      There can be only one dynamic start, so a copy of a dynamic start is considered to be a field pointer
                      at offset 0.

                      Something something linearity.
                     */
                    toStep.copy(
                            qualifiers = toStep.qualifiers + (lhs to ValueQualifier.OffsetQualifier.EncodedFieldPointer(
                                    offset = BigInteger.ZERO,
                                    parent = s,
                                    indexVars = setOf()
                            ))
                    )
                }
            } else if(toStep.nextPointer == s) {
                /*
                  Again, only one distinguished nextPointer
                 */
                toStep.copy(
                        nextPointer = lhs,
                        qualifiers = toStep.qualifiers - s // I feel like this should be a no-op... I'm probably going to regert this
                )
            } else {
                toStep.copy(
                        qualifiers = toStep.qualifiers + ((lhs `to?` toStep.qualifiers[s]) ?: return toStep)
                )
            }
        }

        private fun isSafeBoundFor(o1: TACSymbol.Var, o2: TACSymbol, toStep: EncodingState): Boolean {
            unused(o1)
            unused(o2)
            unused(toStep)
            return true // extremely precise
        }


        override fun stepAssignSub(
            lhs: TACSymbol.Var,
            o1: TACSymbol,
            o2: TACSymbol,
            toStep: EncodingState,
            input: EncodingState,
            whole: Pair<State, PointsToDomain>,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): EncodingState {
            /*
              This is how we detect that we are done encoding in a scratch area (i.e. for a call or a log)
             */
            val toStepPostEncode = if (isScratchEncodeComplete(input, o1, whole.second, o2)) {
                encodeCompletePoints[l.ptr] = IEncoderAnalysis.EncodeCompletePoint(
                    buffer = input.buffer,
                    encoded = EncodeOutput.Scratch
                )
                toStep.copy(varRoots = treapMapOf())
            } else {
                toStep
            }
            if (input.nextPointer == null) run {
                /**
                 * Resolving the type (and therefore the size of a struct) is done lazily. Thus we may compute
                 * a field pointer that (at the time of it's computation) appears to be just another field offset.
                 * However, if it is *used* as a next pointer (i.e., by subtracting a dynamic start from it), and
                 * there are no extant field pointers past it, then we assume it is, in fact, a next pointer.
                 */
                val q1 = toStepPostEncode.qualifiers[o1] as? ValueQualifier.OffsetQualifier.EncodedFieldPointer ?: return@run
                val q2 = toStepPostEncode.qualifiers[o2] as? ValueQualifier.OffsetQualifier.DynamicStart ?: return@run
                check(o1 is TACSymbol.Var && o2 is TACSymbol.Var) {
                    "How did we get values out of a map with a domain TAC vars when $o1 and $o2 aren't vars?"
                }
                if (q1.parent != o2 || o2 != input.currPointer || q2.sort == DynamicSort.ARRAY) {
                    return@run
                }
                if (q2.abiType != null) {
                    ptaInvariant(q2.abiType is LinearizedType.Struct) {
                        "Sort is not array, type is resolved, but the type is not a struct: $q2"
                    }
                    if (q1.offset != q2.abiType.offset.size.toBigInteger() * EVM_WORD_SIZE) {
                        return@run
                    }
                }
                /*
                This is the largest known field pointer for the start in q2
                 */
                if (input.qualifiers.any { (_, it) ->
                        it is ValueQualifier.OffsetQualifier.EncodedFieldPointer && it.parent == o2 && it.offset > q1.offset
                    }) {
                    return@run
                }
                /*
                  Then we have an encoded field pointer that is being subtracted and appears consistent with a next pointer.
                  Update our state accordingly
                 */
                return toStepPostEncode.copy(
                    qualifiers = (toStepPostEncode.qualifiers - o1) + (lhs to ValueQualifier.OffsetPointerFor(
                        parent = o2
                    )),
                    nextPointer = o1,
                    currPointer = null,
                )
            }
            if (input.nextPointer != o1 || o2 !is TACSymbol.Var) {
                return super.stepAssignSub(lhs, o1, o2, toStepPostEncode, input, whole, l)
            }
            val writable = whole.second.arrayState[o2]?.let { d ->
                when (d) {
                    is ArrayStateAnalysis.Value.ScratchPointer -> {
                        ScratchPointer.takeIf {
                            d.index.isConstant && (d.index.c == BigInteger.ZERO || d.index.c == DEFAULT_SIGHASH_SIZE)
                        }
                    }
                    is ArrayStateAnalysis.Value.ElementPointer -> {
                        if (!d.index.isConstant || (d.index.c != BigInteger.ZERO && d.index.c != DEFAULT_SIGHASH_SIZE)) {
                            return@let null
                        }
                        d.arrayPtr.monadicMap {
                            whole.second.pointsToState.store[it] as? WritablePointer
                        }?.uniqueOrNull()
                    }
                    else -> null
                }
            }
            if (writable != null) {
                /*
                   If we are subtracting the beginning of a buffer (i.e., the beginning of an encoding) from
                   the next pointer, the result is an offset for an object at the root.
                 */
                if (writable != toStepPostEncode.buffer || o1 != toStepPostEncode.nextPointer) {
                    return super.stepAssignSub(lhs, o1, o2, toStepPostEncode, input, whole, l)
                }
                return toStepPostEncode.copy(
                    qualifiers = toStepPostEncode.qualifiers + (lhs to ValueQualifier.OffsetForStart)
                )
            }
            /*
              Otherwise we expect to be subtracting from a dynamic target: for structs this is the beginning of the
              struct, for arrays it is the beginning of the data segment. Otherwise the subtraction does not make sense.
             */
            val o2Qual = toStepPostEncode.qualifiers[o2] ?: return super.stepAssignSub(lhs, o1, o2, toStepPostEncode, input, whole, l)
            if (o2Qual !is ValueQualifier.OffsetQualifier.ArrayElemStart && o2Qual !is ValueQualifier.OffsetQualifier.DynamicStart) {
                return super.stepAssignSub(lhs, o1, o2, toStepPostEncode, input, whole, l)
            }
            val base = when (o2Qual) {
                is ValueQualifier.OffsetQualifier.ArrayElemStart -> o2Qual.parent
                is ValueQualifier.OffsetQualifier.DynamicStart -> o2
                else -> `impossible!`
            }
            return toStepPostEncode.copy(
                qualifiers = toStepPostEncode.qualifiers + (lhs to ValueQualifier.OffsetPointerFor(base))
            )
        }
    }

    private fun symEqNextPointer(s: TACSymbol, input: EncodingState, whole: PointsToDomain): Boolean {
        if (input.nextPointer == null) {
            return false
        }

        if (input.nextPointer == s) {
           return true
        }

        return whole.invariants.implies {
            !s `=` !input.nextPointer
        }
    }

    private fun isScratchEncodeComplete(
        input: EncodingState,
        o1: TACSymbol,
        whole: PointsToDomain,
        o2: TACSymbol
    ): Boolean {
        if(symEqNextPointer(o1, input, whole) && input.buffer == ScratchPointer && whole.arrayState[o2]?.let {
            it as? ArrayStateAnalysis.Value.ScratchPointer
        }?.index?.mustEqual(BigInteger.ZERO) == true) {
            return true
        }

        return input.qualifiers[o1]?.tryAs<ValueQualifier.RootQualifier.RootFieldPointer>()?.offset?.let { off1 ->
            input.qualifiers[o2]?.tryAs<ValueQualifier.RootQualifier.RootFieldPointer>()?.offset?.let { off2 ->
                input.varRoots.any {(_, write) -> write.objectPath.isNotEmpty() }
                    && off2 == BigInteger.ZERO
                    && off1 == input.varRoots.size.toBigInteger() * EVM_WORD_SIZE
            }
        } ?: false
    }

    fun isDynamicStartConsistent(
        dynamicState: PointsToDomain,
        dynamicObject: ValueQualifier.OffsetQualifier.DynamicStart,
        rootOffset: BigInteger,
        rootState: PointsToDomain,
    ) : Boolean {
        val rightRoots = rootState.encoderState.encoding?.varRoots ?: return false
        /*
          Find a path of offsets through known constants...
         */
        return findPaths(rightRoots, rootOffset).singleOrNull { path ->
            /*
              If the path found trivially matches the (unresolved) path in the dynamic object, we are done, it is consistent
             */
            when(dynamicObject.path) {
                is Unresolved -> dynamicObject.path == path
                is SerializedPath.Resolved -> {
                    ptaInvariant(dynamicState.encoderState.encoding?.let {
                        it.rootAlignment == null
                    } != true) {
                        "Have resolved ${dynamicObject.path} but the root alignment hasn't been set in the parent state?"
                    }
                    /*
                      Otherwise, in the dynamic object state,
                      check the object root associated with the top-level index for the path...
                     */
                    dynamicState.encoderState.encoding?.varRoots?.get(path.root)?.objectPath?.any { o ->
                        /*
                          Is this root consistent with the dereferences in the inferred path? i.e., do rootState and dynamicState
                          make the same assumptions about the type of the (candidate) root?
                        */
                        if (o is ObjectPathGen.Root) {
                            getABILayoutOfType(o.root, rootState)?.derefFields(path.fields)?.path == dynamicObject.path.o
                        } else {
                            false
                        }
                    } ?: false
                }
            }
        }?.let {
            true
        } ?: false
    }

    /**
     * The [State] has two-levels: information that's always tracked (i.e., the invariants and inferred encoding information)
     * and information that is only present during an encoding process. These semantics are for the "sub-state" [EncodingState]
     */
    private val encodingSemantics = object : AbstractStatementInterpreter<EncodingState?, Pair<State, PointsToDomain>>() {
        override fun stepExpression(lhs: TACSymbol.Var, rhs: TACExpr, toStep: EncodingState?, input: EncodingState?, whole: Pair<State, PointsToDomain>, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): EncodingState? {
            if(toStep == null) {
                return null
            }
            check(input != null)
            return semantics.stepExpression(lhs, rhs, toStep, input, whole, l)
        }

        override fun forget(lhs: TACSymbol.Var, toStep: EncodingState?, input: EncodingState?, whole: Pair<State, PointsToDomain>, l: LTACCmd): EncodingState? {
            if(toStep == null) {
                return null
            }
            check(input != null)
            return toStep.kill(lhs)
        }

        private fun bindingOfArray(
            k: TACSymbol.Var, ind: IntValue
        ) : Pair<BigInteger?, Pair<TACSymbol.Var, ValueQualifier.RootQualifier.RootFieldPointer>> {
            val iVal = ind.c
            val binding = (k to ValueQualifier.RootQualifier.RootFieldPointer(
                offset = iVal - (iVal.mod(EVM_WORD_SIZE))
            ))
            return if(iVal == BigInteger.ZERO) {
                null to binding
            } else {
                iVal.mod(EVM_WORD_SIZE) to binding
            }
        }

        fun findArrayPointers(toStep: EncodingState?, whole: Pair<State, PointsToDomain>): EncodingState? {
            if (toStep == null) {
                return null
            }

            /*
              Lazily find and qualify array pointers that we "missed" due to lazy detection of encoding.

              TODO(jtoman): this looks pretty eager????
             */
            val toAssign = whole.second.arrayState.mapNotNull { (k, v) ->
                if (v is ArrayStateAnalysis.Value.ScratchPointer && toStep.buffer == ScratchPointer && v.index.isConstant && k !in toStep.qualifiers) {
                    bindingOfArray(k, v.index)
                } else if (v is ArrayStateAnalysis.Value.ElementPointer && v.arrayPtr.any {
                        whole.second.pointsToState.store[it] == toStep.buffer
                    } && v.index.isConstant && k !in toStep.qualifiers) {
                    bindingOfArray(k, v.index)
                } else {
                    null
                }
            }.filter { (_, binding) ->
                val (_, rfp) = binding
                // this is an array pointer that lives within the "dynamic" portion of the encoded buffer, i.e.,
                // past the end of where the known offsets lie
                toStep.varRoots.none { (_, tlw) ->
                    tlw.const != null && tlw.const < rfp.offset && tlw.isDefinitelyOffset
                }
            }.takeIf {
                it.isNotEmpty()
            } ?: return toStep
            val (alignments, bindings) = toAssign.unzip()
            return alignments.fold(toStep) { acc: EncodingState?, align ->
                if(align == null) {
                    return@fold acc
                }
                acc?.resolveAlignment(align)
            }?.let { aligned ->
                aligned.copy(
                    qualifiers = aligned.qualifiers + bindings
                )
            }
        }

        override fun stepCommand(l: LTACCmd, toStep: EncodingState?, input: EncodingState?, whole: Pair<State, PointsToDomain>): EncodingState? {
            val toStep_ = findArrayPointers(toStep, whole)
            val input_ = findArrayPointers(input, whole)
            return if(l.cmd is TACCmd.Simple.AssigningCmd.ByteStore && toStep_ != null && input_ != null) {
                stepWrite(
                        m = toStep_,
                        whole = whole.second,
                        outer = whole.first,
                        ltacCmd = l.narrow()
                )
            } else if(l.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && l.cmd.rhs is TACExpr.Sym.Var && l.cmd.rhs.s == TACKeyword.MEM64.toVar()) {
                /*
                At a read of the free pointer, if we are tracking a buffer already, ensure the read is of the same "sort"
                 */
                if (toStep_ != null) {
                    if (l.ptr !in scratchSites && l.ptr !in allocSites) {
                        return toStep_ // weird! this is likely unreachable: the MemoryStepper will fail if it finds an unclassified site
                    }
                    // verify this is just another read of the same
                    if (toStep_.buffer == ScratchPointer) {
                        if (l.ptr !in scratchSites) {
                            return null
                        }
                        return toStep_
                    } else {
                        ptaInvariant(whole.second.pointsToState.h.allocStack.isNotEmpty()) {
                            "Have that we are initializing a byte init pointer ${toStep_.buffer} but pta thinks there are not active allocations"
                        }
                        ptaInvariant(toStep_.buffer is InitializationPointer.ByteInitPointer) {
                            "Encoding to an address ${toStep_.buffer} which is not a byte init pointer"
                        }
                        ptaInvariant(whole.second.pointsToState.h.allocStack.lastOrNull() == toStep_.buffer.initAddr) {
                            "Encoding to a byte init buffer ${toStep_.buffer} which has sub-allocations"
                        }
                        if (toStep_.buffer.initAddr != allocSites[l.ptr]) {
                            logger.warn {
                                "Hit a nested allocation during allocation of byte buffer ${toStep_.buffer}; this is likely wrong"
                            }
                            return null
                        }
                        return toStep_
                    }
                /*
                   Otherwise, we aren't tracking a buffer, and this looks like the beginning of one, so initialize the state
                 */
                } else if (scratchSites[l.ptr] == Optional.of(BigInteger.ZERO)) {
                    EncodingState.init(ScratchPointer)
                } else {
                    /*
                      Ditto, but only track packed byte arrays
                     */
                    val arr = allocSites[l.ptr]?.takeIf {
                        it.sort is AllocationAnalysis.Alloc.PackedByteArray
                    } ?: return null
                    return EncodingState.init(InitializationPointer.ByteInitPointer(InitAddress(arr), mayAdded = false, mustAdded = false))
                }
            } else if(l.cmd is TACCmd.Simple.AssumeCmd && toStep_ != null) {
                /* this is here specifically to interpret the commands inserted by the loop interpolation pass.
                   Sometimes the serialization scheme computes the next pointer as part of the execution of the loop,
                   i.e., after fully copying the contents of an array into a point in the buffer, the "output pointer"
                   of the loop actually points to the end of the encoding of the array, i.e., it is a next pointer.

                   This is a *nightmare* to detect "syntactically", but luckily the statements generated by the loop interpolation
                   will "look like" directly computing the next pointer. However, the end result of this computation is placed
                   into an "assume!..." variable, which is never used again. So, we interpret assume statements and the conditions
                   they encode so that when we have
                   `v1 == NEXT` (where NEXT is a variable that has the role of nextPointer).
                   We then assume that we are transferring the role of nextPointer from NEXT to v1.
                 */
                if (l.cmd.cond !is TACSymbol.Var) {
                    return super.stepCommand(l, toStep_, input_, whole)
                }
                val bound = whole.second.boundsAnalysis[l.cmd.cond]?.let {
                    it as? QualifiedInt
                }?.qual?.asSequence()?.filterIsInstance<IntQualifier.ConditionVar>()?.filter {
                    it.condition == ConditionQualifier.Condition.EQ && (it.op1 == toStep_.nextPointer || it.op2 == toStep_.nextPointer) &&
                            it.op1 is TACSymbol.Var && it.op2 is TACSymbol.Var
                }?.map {
                    (if (it.op1 == toStep_.nextPointer) {
                        it.op2
                    } else {
                        check(it.op2 == toStep_.nextPointer)
                        it.op1
                    }) as TACSymbol.Var
                }?.toList()?.uniqueOrNull() ?: return super.stepCommand(l, toStep_, input_, whole)
                toStep_.copy(
                        nextPointer = bound
                )
            } else if(l.cmd is TACCmd.Simple.ByteLongCopy && toStep_ != null) {
                stepLongCopy(
                    toStep = toStep_,
                    whole = whole.second,
                    outer = whole.first,
                    where = l.narrow()
                )
            } else if(l.cmd is TACCmd.Simple.LogCmd) {
                if(toStep_ != null && whole.second.arrayState[l.cmd.sourceOffset]?.let {
                        it as? ArrayStateAnalysis.Value.ScratchPointer
                    }?.index == IntValue.Constant(BigInteger.ZERO) && toStep_.buffer is ScratchPointer) {
                    return null
                }
                super.stepCommand(l, toStep, input_, whole)
            } else {
                super.stepCommand(l, toStep_, input_, whole)
            }
        }
    }

    override fun consumeLoopSummary(
        encoderState: State,
        ppNextState: PointsToDomain,
        s: LoopCopyAnalysis.LoopCopySummary,
        finalCmd: LTACCmd
    ): State {
        return encoderState.copy(
            encoding = encoderState.encoding?.let { toStep ->
                stepCopyOperation(
                    copy = object : CopyOperation {
                        override val sourceBase: TACSymbol.Var
                            get() = s.sourceMap
                        override val sourceOffset: TACSymbol
                            get() = s.inPtr.first()
                        override val destOffset: TACSymbol
                            get() = s.outPtr.first()
                        override val len: TACSymbol
                            get() = s.lenVars.first()
                        override val lengthType: LengthType
                            get() = LengthType.Logical(s.assumedSize)
                        override val isSummarizedLoop: Boolean
                            get() = true
                    },
                    whole = ppNextState,
                    where = finalCmd,
                    encodingState = toStep
                )
            }
        )
    }

    /**
     * It is possible to pass calldata encoded objects directly into an encoded object. *Usually* we can get away by just
     * using information computed by the decoder analysis (i.e., using its map from buffer access paths to object paths
     * and the readfrom qualifiers). However, for arrays solidity will use bytelongcopy directly from calldata. So we have
     * to detect that.
     *
     * TODO(jtoman): in some other (not terribly well studied or understood yet) circumstances, solidity will use bytelongcopy
     *   to copy other objects.
     */
    private fun stepLongCopy(toStep: EncodingState, whole: PointsToDomain, outer: State, where: LTACCmdView<TACCmd.Simple.ByteLongCopy>): EncodingState? {
        unused(outer)
        if(TACMeta.MCOPY_BUFFER in where.cmd.dstBase.meta) {
            if(where.cmd.srcBase != TACKeyword.MEMORY.toVar()) {
                logger.warn {
                    "Very suspicious: have a long copy to mcopy buffer that does not have memory as its source: $where"
                }
                return toStep
            }
            val srcOffset = (where.cmd.srcOffset as? TACSymbol.Var) ?: return toStep.also {
                logger.warn {
                    "Have mcopy from non-variable source $where"
                }
            }
            if(numeric.interpAsConstant(whole, where.wrapped, where.cmd.dstOffset) != BigInteger.ZERO) {
                logger.warn {
                    "Very suspicious: have long copy to mcopy buffer that is not targeting offset 0 $where"
                }
                return toStep
            }
            return toStep.copy(
                copyBuffers = toStep.copyBuffers + (where.cmd.dstBase to MCopyOperands(
                    srcOffset = srcOffset,
                    srcLength = where.cmd.length
                ))
            )
        }
        return stepCopyOperation(copy = object : CopyOperation {
            override val sourceBase: TACSymbol.Var
                get() = where.cmd.srcBase
            override val sourceOffset: TACSymbol
                get() = where.cmd.srcOffset
            override val destOffset: TACSymbol
                get() = where.cmd.dstOffset
            override val len: TACSymbol
                get() = where.cmd.length
            override val lengthType: LengthType
                get() = LengthType.Physical
            override val isSummarizedLoop: Boolean
                get() = false

        }, encodingState = toStep, whole = whole, where = where.wrapped)
    }

    sealed interface LengthType {
        object Physical : LengthType
        data class Logical(val elemSize: BigInteger) : LengthType
    }

    /**
     * Carrier class for the various ways we represent copy operations (staged mcopy, calldata copies, summaries).
     *
     * [isSummarizedLoop]  enables some specialized handling that should only be done if the source of the
     * copy is a copy loop.
     * [lengthType] indicates what [len] represents, the number of bytes copied, or the number of elements (see [LengthType]).
     */
    private interface CopyOperation {
        val sourceBase: TACSymbol.Var
        val sourceOffset: TACSymbol
        val destOffset: TACSymbol
        val len: TACSymbol
        val lengthType: LengthType
        val isSummarizedLoop: Boolean
    }

    private fun stepCopyOperation(
        copy: CopyOperation,
        encodingState: EncodingState,
        whole: PointsToDomain,
        where: LTACCmd
    ) : EncodingState? {
        if(copy.sourceBase == TACKeyword.CALLDATA.toVar()) {
            return stepCalldataCopyOperation(copy, encodingState, whole, where)
        } else if(TACMeta.MCOPY_BUFFER in copy.sourceBase.meta) {
            val copySource = encodingState.copyBuffers[copy.sourceBase] ?: return null.andWarn {
                "Failed to find source of mcopy operation in abstract state $where"
            }
            if(copySource.srcLength != copy.len) {
                return null.andWarn {
                    "Copy lengths mismatch between source of mcopy and dest $copySource vs ${copy.len} @ $where"
                }
            }
            return stepMemoryCopyOperation(object : CopyOperation by copy {
                override val sourceOffset: TACSymbol
                    get() = copySource.srcOffset
            }, encodingState, whole, where)
        } else if(copy.sourceBase == TACKeyword.MEMORY.toVar()) {
            if(!copy.isSummarizedLoop) {
                return null.andWarn {
                    "Have copy from memory that is not a copy loop @ $where, this is deeply unexpected"
                }
            }
            return stepMemoryCopyOperation(copy, encodingState, whole, where)
        } else {
            return null.andWarn {
                "Unrecognized copy operation @ $where"
            }
        }
    }

    private fun stepCalldataCopyOperation(
        copy: CopyOperation,
        encodingState: EncodingState,
        whole: PointsToDomain,
        where: LTACCmd
    ): EncodingState? {
        return stepCopyOperationGen(copyOperation = copy, toStep = encodingState, where = where, whole = whole, accessor = object : SourceArrayAccessor<DecoderAnalysis.AbstractDomain.BufferIndices.DynamicStart> {
            override fun getSourceArrayData(v: TACSymbol.Var): DecoderAnalysis.AbstractDomain.BufferIndices.DynamicStart? {
                return whole.decoderState.qualifiers[v]?.let {
                    it as? DecoderAnalysis.AbstractDomain.BufferIndices.ArrayElemStart
                }?.basePointer?.let(whole.decoderState.qualifiers::get)?.let {
                    it as? DecoderAnalysis.AbstractDomain.BufferIndices.DynamicStart
                }?.takeIf {
                    it.knownType != null && it.strideSize != null && it.mustBeArray
                }
            }

            override fun getObjectPaths(v: TACSymbol.Var): Set<ObjectPath>? {
                return decoderAnalysis.getCalldataReadPath(v, whole)
            }

            override fun knownElementSize(data: DecoderAnalysis.AbstractDomain.BufferIndices.DynamicStart): BigInteger? {
                if(data.knownType is HeapType.ByteArray) {
                    return BigInteger.ONE
                }
                return data.strideSize!!
            }

            override fun getSourceArrayLengths(v: DecoderAnalysis.AbstractDomain.BufferIndices.DynamicStart): Set<TACSymbol.Var> {
                return whole.decoderState.qualifiers.keysMatching { _, av ->
                    av is DecoderAnalysis.AbstractDomain.ReadFrom && whole.decoderState.qualifiers[av.index]?.let {
                        it as? DecoderAnalysis.AbstractDomain.BufferIndices.DynamicStart
                    }?.path == v.path
                }.toSet()
            }

        })
    }

    /**
     * Interface used to get information about the source array being copied from, while
     * abstracting where and how that array is being accessed (in memory vs calldata, long copy
     * vs. copy loop). [T] is the type of "array" data, which is used to answer further queries about the
     * array.
     */
    private interface SourceArrayAccessor<T> {
        /**
         * Get the representation of the array, whose element data starts at [v] (NB: [v] is NOT
         * a pointer to the array itself, but its data).
         */
        fun getSourceArrayData(v: TACSymbol.Var): T?

        /**
         * The set of variables which hold the length of the array in [v].
         */
        fun getSourceArrayLengths(v: T): Set<TACSymbol.Var>

        /**
         * Get arbitrary object paths for [v]. Note that this doesn't have anything to do with [T], but it should
         * consult the same "source" as is used when looking up array data (i.e., calldata object paths for calldata arrays,
         * object paths for in-memory arrays).
         */
        fun getObjectPaths(v: TACSymbol.Var): Set<ObjectPath>?
        fun knownElementSize(data: T): BigInteger?
    }

    private fun <T> stepCopyOperationGen(
        copyOperation: CopyOperation,
        toStep: EncodingState,
        accessor: SourceArrayAccessor<T>,
        whole: PointsToDomain,
        where: LTACCmd,
    ) : EncodingState? {
        val dstLoc = copyOperation.destOffset as? TACSymbol.Var ?: return null.andWarn {
            "At copy @ $where, destination offset was not a variable ${copyOperation.destOffset}"
        }
        val (which, _) = getWriteTarget(dstLoc, whole) ?: return null.andWarn {
            "At copy @ $where, destination wasn't a known array pointer $dstLoc"
        }
        if(which != toStep.buffer) {
            return toStep
        }
        val src = copyOperation.sourceOffset as? TACSymbol.Var?: return null.andWarn {
            "At copy @ $where, source offset was not a variable ${copyOperation.sourceOffset}"
        }
        val dstAV = toStep.qualifiers[dstLoc] ?: return null.andWarn {
            "No qualifiers for output $dstLoc at $where, despite it being the buffer we're allocating"
        }
        if(dstAV !is ValueQualifier.RootQualifier && dstAV !is ValueQualifier.OffsetQualifier) {
            return null.andWarn {
                "Unexpected form of qualifiers for copy destination $dstLoc @ $where, $dstAV"
            }
        }
        val dstStart = dstAV as? ValueQualifier.OffsetQualifier.ArrayElemStart ?: return null.andWarn {
            "At copy $where, output is not a known array elem start qualifier $dstAV"
        }
        val dstParent = toStep.qualifiers[dstStart.parent]?.let {
            it as? ValueQualifier.OffsetQualifier.DynamicStart
        } ?: return null.andWarn {
            "At copy $where, parent of elem start at $dstLoc was not a dynamic start"
        }
        if(dstParent.path !is SerializedPath.Resolved) {
            return null.andWarn {
                "Trying to copy data into an array at $dstLoc @ $where before we've resolved its path (i.e., written its length)"
            }
        }


        val sourceData = accessor.getSourceArrayData(src) ?: return null.andWarn {
            "At copy $where, source $src is not known to contain an array object"
        }

        val knownElementSize = accessor.knownElementSize(sourceData) ?: return null.andWarn {
            "No element size known for source array $sourceData"
        }

        val sourceArrayLengths = accessor.getSourceArrayLengths(sourceData)
        if(sourceArrayLengths.isEmpty()) {
            return null.andWarn {
                "Couldn't find any lengths associated with source array at $src"
            }
        }

        val copyScaleAmount = when(val l = copyOperation.lengthType) {
            LengthType.Physical -> BigInteger.ONE
            is LengthType.Logical -> l.elemSize
        }

        if(sourceArrayLengths.none { lenVar ->
            accessor.getObjectPaths(lenVar)?.any { path ->
                path is ObjectPathGen.ArrayLength && path.parent == dstParent.path.o
            } == true && whole.invariants implies {
                !copyOperation.len * copyScaleAmount `=` !lenVar * knownElementSize
            }
        }) {
            return null.andWarn {
                "Could not prove we copied the whole array with ${copyOperation.len} @ $where with source array lengths: $sourceArrayLengths"
            }
        }
        val nextWriteState = if(knownElementSize.mod(EVM_WORD_SIZE) == BigInteger.ZERO || copyOperation.isSummarizedLoop) {
            EncodingState.ExpectNextWriteZero.Optional
        } else {
            EncodingState.ExpectNextWriteZero.Required
        }
        return toStep.copy(
            expectNextWriteZero = nextWriteState
        )
    }

    private fun stepMemoryCopyOperation(
        copyOperation: CopyOperation,
        encodingState: EncodingState,
        whole: PointsToDomain,
        where: LTACCmd
    ): EncodingState? {
        return stepCopyOperationGen(
            copyOperation = copyOperation,
            whole = whole,
            where = where,
            toStep = encodingState,
            accessor = MemorySourceArrayAccessor(whole)
        )
    }

    inner class MemorySourceArrayAccessor(private val whole: PointsToDomain) : SourceArrayAccessor<TACSymbol.Var> {
        override fun getSourceArrayData(v: TACSymbol.Var): TACSymbol.Var? {
            return (whole.pointsToState.store[v] as? Pointer.ArrayElemStart)?.let { _ ->
                whole.arrayState[v]?.let {
                    it as? ArrayStateAnalysis.Value.ElementPointer
                }?.takeIf {
                    it.index == IntValue.Constant(BigInteger.ZERO)
                }?.arrayPtr?.firstOrNull()
            }
        }

        override fun getObjectPaths(v: TACSymbol.Var): Set<ObjectPath>? {
            return whole.objectPath[v]
        }

        override fun knownElementSize(data: TACSymbol.Var): BigInteger? {
            return pointerSem.getElementSize(data, whole.pointsToState)?.takeIf {
                pointerSem.getHeapType(data, whole)?.let { ty ->
                    when(ty) {
                        is HeapType.ByteArray -> true
                        is HeapType.Array -> ty.elementType == HeapType.Int
                        else -> false
                    }
                } == true
            }
        }

        override fun getSourceArrayLengths(v: TACSymbol.Var): Set<TACSymbol.Var> {
            val directLenVars = whole.boundsAnalysis.keysMatching { _, id ->
                id is QualifiedInt && id.qual.any { iq ->
                    iq is IntQualifier.LengthOfArray && (whole.invariants implies {
                        !iq.arrayVar `=` !v
                    } || iq.arrayVar == v)
                }
            }.toTreapSet()
            return directLenVars + (whole.invariants matches {
                v("eq") `=` v("other") { lv ->
                    lv is LVar.PVar && lv.v in directLenVars
                }
            }).map { m ->
                (m.symbols["eq"] as LVar.PVar).v
            }
        }
    }

    private val topLevelSemantics = object : AbstractAbstractInterpreter<PointsToDomain, State>() {
        override val statementInterpreter: IStatementInterpreter<State, PointsToDomain> = object : IStatementInterpreter<State, PointsToDomain> {
            override fun stepCommand(l: LTACCmd, toStep: State, input: State, whole: PointsToDomain): State {
                val r1 = encodingSemantics.stepCommand(whole = input to whole, input = input.encoding,toStep = toStep.encoding, l = l)
                val r2 = toStep.finalizedState
                return State(
                        encoding = r1,
                        finalizedState = r2
                )
            }
        }

        override fun killLHS(lhs: TACSymbol.Var, s: State, w: PointsToDomain, narrow: LTACCmdView<TACCmd.Simple.AssigningCmd>): State {
            return State(
                    encoding = s.encoding?.kill(lhs),
                    finalizedState = s.finalizedState.retainAll { (k, v) ->
                        k != lhs && !v.buffer.values.any { vv ->
                            !vv.objectPath.any {
                                it.rootVar == lhs
                            }
                        }
                    }
            )
        }

        override val pathSemantics: IPathSemantics<State, PointsToDomain> = TrivialPathSemantics()
        override fun postStep(stepped: State, l: LTACCmd): State = stepped
        override fun project(l: LTACCmd, w: PointsToDomain): State = w.encoderState
    }

    /**
     * Check whether the invariants in [inv] can prove that [nextPointer] = [dyn].addBase + [writeValue].
     * [writeValue] is expected to be a symbol that was written into some location [writeLoc]
     * of the dynamic object represented by [dyn]. If the equation above is proven true, then we conclude
     * that [nextPointer] is in fact a child dynamic object of [dyn], and update the qualifiers appropriately,
     * using [dynamicFromBlock]
     */
    private fun matchAdditionToWrite(
            inv: LinearInvariants,
            writeValue: TACSymbol,
            writeLoc: OffsetLocation,
            nextPointer: TACSymbol.Var,
            dyn: DynamicObject,
            m: EncodingState
    ) : EncodingState? {
        return if(inv implies {
            !nextPointer `=` !dyn.addBase + when(writeValue) {
                is TACSymbol.Var -> LinearTerm(
                        listOf(
                            LinearAtom(!writeValue, BigInteger.ONE)
                        )
                )
                is TACSymbol.Const -> LinearTerm(listOf(), writeValue.value)
            }
        }) {
            /**
             * In some *awful* cases (like those seen in the DynamicStructAndStatic.sol test)
             * solidity will generate a field pointer that is beyond the end of the struct.
             * For example, when encoding
             * struct Yolo {
             *    uint[][3] swag;
             *    uint foo;
             * }
             * solidity may generate:
             * ```
             * swagNext = startOfYolo + 0xa0;
             * mem[startOfYolo] = 0x40;
             * startOfSwag = startOfYolo + 0x40;
             * ```
             *
             * When we determine that startOfSwag is actually a dynamic child, then we can be certain that the constant
             * 0x40 gives us the size of the yolo (we haven't resolved it yet). Thus we can immediately determine that
             * swagNext is not in fact a field pointer for yolo with offset 0xa0, but actually an encoded field pointer
             * of swag, with offset 0x60.
             *
             * (This is also not actually true, but see the `stepAssignSub` function for how we lazily detect that swagNext
             * is actually a next pointer.)
             */
            val toTransition = if (writeValue is TACSymbol.Const) {
                m.qualifiers.mapNotNull { (k, v) ->
                    (v as? ValueQualifier.OffsetQualifier.EncodedFieldPointer)?.takeIf {
                        it.parent == dyn.dynVar && it.offset >= writeValue.value
                    }?.let {
                        k to ValueQualifier.OffsetQualifier.EncodedFieldPointer(
                            offset = it.offset - writeValue.value,
                            parent = nextPointer,
                            indexVars = setOf()
                        )
                    }
                }
            } else {
                listOf()
            }
            m.copy(
                    qualifiers = m.qualifiers + toTransition + (nextPointer to dynamicFromBlock(writeLoc, dyn.dyn))
            ).transitionCurr(nextPointer)
        } else {
            null
        }
    }

    /**
     * Given a parent dynamic object [parent], create a
     * child [analysis.pta.abi.EncoderAnalysis.ValueQualifier.OffsetQualifier.DynamicStart] at the location provided
     * by [writeLoc]. If [parent] has type/path information, this is properly propagated into the child object.
     */
    private fun dynamicFromBlock(writeLoc: OffsetLocation, parent: ValueQualifier.OffsetQualifier.DynamicStart): ValueQualifier.OffsetQualifier.DynamicStart {
        return if(writeLoc is OffsetLocation.Elem) {
            /*
              Q: Why can we assume that the array is resolved?
              A: If we have written an offset, that means we've written data, which by our assumption that array data is always
              written after the length of the array means that we must have resolved the array (because we can immediately
              resolve an array after writing the length).
             */
            ptaInvariant(parent.sort == DynamicSort.ARRAY &&
                    parent.abiType is LinearizedType.Array &&
                    parent.abiType.cont.isDynamic &&
                    parent.path is SerializedPath.Resolved &&
                    parent.path.o == parent.abiType.path) {
                "Trying to a create a dynamic child of array $parent but the paths/types don't seem right"
            }
            ptaInvariant(parent.abiType.cont.path == ObjectPathGen.ArrayElem(parent.abiType.path)) {
                "Path mismatch: ${parent.abiType.cont.path} isn't a direct child of parent's path ${parent.abiType.path}"
            }
            ValueQualifier.OffsetQualifier.DynamicStart(
                    abiType = parent.abiType.cont,
                    lastWrittenOffset = null,
                    sort = parent.abiType.cont.toSort()!!,
                    path = SerializedPath.Resolved(parent.abiType.cont.path),
                    indexVars = setOf()
            )
        } else if(writeLoc is OffsetLocation.StaticArray) {
            ptaInvariant(parent.abiType is LinearizedType.Struct && parent.path is SerializedPath.Resolved) {
                /*
                Why is this true? Well, we assume objects are serialized depth-first, so if we have a static array of dynamic
                objects, in the process of fully serializing that object we must have written an array length, which means
                we could resolve the array *and all its parents*, including this struct.
                */
                "Parent $parent is not a struct, or hasn't yet been resolved (we should not stride a dynamic pointer until we have resolved at least one element)"
            }
            ptaInvariant(parent.abiType.offset.values.monadicFold { a, b ->
                a.takeIf { it.equivModuloPath(b) }
            } != null) {
                "Values within the parent $parent have different shapes"
            }
            /*
              From the path information of the parent, infer the path of the static fields.
             */
            val staticElem = parent.abiType.offset.values.first().staticFieldOf(parent.path.o)
            ValueQualifier.OffsetQualifier.DynamicStart(
                    abiType = staticElem,
                    path = SerializedPath.Resolved(staticElem.path),
                    indexVars = setOf(),
                    sort = staticElem.toSort(),
                    lastWrittenOffset = null
            )
        } else {
            ptaInvariant(writeLoc is OffsetLocation.Field) { "Forgotten case: $writeLoc was expected to be Field" }
            if(parent.abiType == null) {
                ptaInvariant(parent.path is Unresolved) { "Have resolved path but not type in parent $parent" }
                ValueQualifier.OffsetQualifier.DynamicStart(
                        abiType = null,
                        sort = null,
                        indexVars = setOf(),
                        path = parent.path + writeLoc.offset,
                        lastWrittenOffset = null
                )
            } else {
                ptaInvariant(parent.abiType is LinearizedType.Struct && parent.path is SerializedPath.Resolved) {
                    "Resolving field element of $parent which is not a struct, or has a type but no path" }
                val ty = parent.abiType.offset[writeLoc.offset] ?: throw AnalysisFailureException("Write out ot bounds @ $writeLoc for parent ${parent.path}")
                ptaInvariant(ty.isDynamic) {
                    "Dynamic block at $writeLoc is not dynamic type: $ty"
                }
                ValueQualifier.OffsetQualifier.DynamicStart(
                        abiType = ty,
                        sort = ty.toSort()!!,
                        indexVars = setOf(),
                        path = SerializedPath.Resolved(ty.path),
                        lastWrittenOffset = null
                )
            }
        }
    }

    /*
      TODO(jtoman): this is redundant now given the eager detection of rootfields???
     */
    private interface ElementFinder {
        fun elementWithIndex(d: BigInteger) : Set<TACSymbol.Var>
    }

    private class AllocElementFinder(val whole: PointsToDomain, val baseArrays: Set<TACSymbol.Var>, val sigAdjust: BigInteger) : ElementFinder {
        override fun elementWithIndex(d: BigInteger) : Set<TACSymbol.Var> {
            return whole.arrayState.keysMatching { _, v->
                v is ArrayStateAnalysis.Value.ElementPointer && v.index.isConstant && v.index.c == sigAdjust + d && v.arrayPtr.containsAny(baseArrays)
            }.toSet()
        }
    }

    private class ScratchElementFinder(val whole: PointsToDomain, val sigAdjust: BigInteger) : ElementFinder {
        override fun elementWithIndex(d: BigInteger): Set<TACSymbol.Var> {
            return whole.arrayState.keysMatching { _, value ->
                value is ArrayStateAnalysis.Value.ScratchPointer && value.index.isConstant && value.index.c == sigAdjust + d
            }.toSet()
        }
    }

    private fun elementFinderFor(whole: PointsToDomain, encoderState: EncodingState, sigAdjust: BigInteger) : ElementFinder? {
        return if(encoderState.buffer == ScratchPointer) {
            ScratchElementFinder(whole, sigAdjust)
        } else {
            val baseArrays = whole.pointsToState.store.keysMatching { _, pts ->
                pts ==  encoderState.buffer
            }.toSet().takeIf { it.isNotEmpty() } ?: return null
            AllocElementFinder(whole, baseArrays, sigAdjust)
        }
    }

    private data class WriteValue(
        val constValue: BigInteger?,
        val writtenQual: ValueQualifier?,
        val writtenPaths: Set<ObjectPath>,
        val lengthWriteFor: Set<ObjectPathAnalysis.ObjectRoot>,
        val symbol: TACSymbol
    )

    private fun getWriteTarget(loc: TACSymbol.Var, whole: PointsToDomain) : Pair<WritablePointer, BigInteger?>? {
        return when(val d = whole.arrayState[loc] ?: return null) {
            is ArrayStateAnalysis.Value.ScratchPointer -> {
                ScratchPointer to d.index.takeIf { it.isConstant }?.c?.mod(EVM_WORD_SIZE)
            }
            is ArrayStateAnalysis.Value.ElementPointer -> {
                val baseArrays = d.arrayPtr
                val basePointer = baseArrays.monadicMap {
                    whole.pointsToState.store[it] as? WritablePointer
                }?.uniqueOrNull() ?: return null
                basePointer to d.index.takeIf { it.isConstant }?.c?.mod(EVM_WORD_SIZE)
            }
            else -> return null
        }
    }

    private fun checkZeroWrite(
        m: EncodingState, whole: PointsToDomain, ltacCmd: LTACCmdView<TACCmd.Simple.AssigningCmd.ByteStore>
    ): Boolean {
        val c = ltacCmd.cmd
        val mustWriteZero = m.expectNextWriteZero == EncodingState.ExpectNextWriteZero.Required

        fun logIfMust(f : () -> String) {
            if (mustWriteZero) {
                logger.info(f)
            }
        }

        if (c.value.let { it as? TACSymbol.Const }?.value != BigInteger.ZERO) {
            logIfMust {
                "Expected a write of zero, but got ${c.value} @ $ltacCmd"
            }
            return false
        }

        /*
        If we have a next pointer (i.e., a variable that must point to the end of the array) then we must be
        writing there
         */
        if (m.nextPointer != null) {
            if (mustWriteZero && c.loc != m.nextPointer) {
                logIfMust {
                    "Expected a write of 0 to ${m.nextPointer}, write location in ${c.loc} @ $ltacCmd"
                }
                return false
            }
        } else if (m.currPointer == null) {
            logIfMust {
                "Could not determine if zero write is at correct location @ $ltacCmd"
            }
            return false
        } else {
            /*
             Otherwise, we copied a byte array. In that case, the end of where we wrote array data
             isn't actually the next pointer: remember that for bytes arrays we have to round up.

             So see if we're actually writing at the end of the array segment, i.e. the base of the array
             plus 32 plus length.
             */
            val ty = m.qualifiers[m.currPointer]?.let {
                it as? ValueQualifier.OffsetQualifier.DynamicStart
            }?.takeIf {
                it.sort == DynamicSort.ARRAY && it.abiType is LinearizedType.Array && it.abiType.isByte
            } ?: run {
                logIfMust {
                    "Current object ${m.qualifiers[m.currPointer]} is not known to be a byte pointer, failing @ $ltacCmd"
                }
                return false
            }
            if (lengthVarsForEncodedArray(ty, whole = whole)?.none {
                    whole.invariants implies {
                        !c.loc `=` !m.currPointer + !it + 32
                    }
                } ?: true) {
                logIfMust {
                    "Could not prove we are writing to immediately after byte array elements @ $ltacCmd"
                }
                return false
            }
        }
        return true
    }

    private fun stepWrite(m: EncodingState, outer: State, whole: PointsToDomain, ltacCmd: LTACCmdView<TACCmd.Simple.AssigningCmd.ByteStore>) : EncodingState? {
        val c = ltacCmd.cmd
        if(c.base != TACKeyword.MEMORY.toVar() || c.loc !is TACSymbol.Var) {
            return m
        }
        // ignore length writes
        if(whole.pointsToState.store[c.loc]?.let {
                    it as? InitializationPointer.LengthFieldInit
                }?.mayAdded == false) {
            return m
        }
        /*
          If we encoding a function call, then logically index 0 in the encoding is actually
          at index 4, etc. etc. It is very convenient to just always assume that the encoding
          begins at index 0, so sigAdjust tells us how to adjust the logical indices reported by the ArrayStateAnalysis
          to make this view of encoding indices hold.
         */
        val (basePointer, sigAdjust) = getWriteTarget(c.loc, whole) ?: return null.andInfo {
            "Write to ${c.loc} @ $ltacCmd could not be resolved to a unique target"
        }
        if(m.buffer != basePointer) {
            return m
        }
        val killBaseBuffer by lazy {
            logger.warn {
                "Killing state at write @ $ltacCmd"
            }
            null
        }
        /*
          We expected the next operation to be the computation of a child object pointer (because we wrote
           what should have been an offset) but here we are writing something else. Die.
         */
        if(m.expectNext) {
            logger.info {
                "Expected a computation of the next pointer, but have a write @ $ltacCmd"
            }
            return killBaseBuffer
        }

        /* If we might be expecting a zero write & we see one, we can stop */
        if (m.expectNextWriteZero != EncodingState.ExpectNextWriteZero.NotExpected) {
            if (checkZeroWrite(m, whole, ltacCmd)) {
                return m.copy(expectNextWriteZero = EncodingState.ExpectNextWriteZero.NotExpected)
            } else if (m.expectNextWriteZero == EncodingState.ExpectNextWriteZero.Required) {
                logger.info {
                    "Could not prove that $ltacCmd was the required zero write"
                }
                return killBaseBuffer
            }
        }

        val postZeroWrite = m.copy(expectNextWriteZero = EncodingState.ExpectNextWriteZero.NotExpected)

        val q_ = postZeroWrite.qualifiers[c.loc]?.let {
            it as? ValueQualifier.OffsetQualifier
        }
        val rootQual : ValueQualifier.RootQualifier? = postZeroWrite.qualifiers[c.loc]?.let {
            it as? ValueQualifier.RootQualifier
        }
        /*
          If we aren't writing to an offsetqualifier or a rootqualifier, something has gone *very* wrong.
         */
        if((q_ == null) == (rootQual == null)) {
            logger.info {
                "Had both root and offset info, or neither write was tracked $q_ & $rootQual @ $ltacCmd"
            }
            return killBaseBuffer
        }
        val isConst = numeric.interpAsConstant(whole, ltacCmd = ltacCmd.wrapped, value = c.value)
        val writtenQual = (c.value as? TACSymbol.Var)?.let(postZeroWrite.qualifiers::get)
        /*
         If the value is tagged as cleaned, retrieve the path of the value that was cleaned
         */
        val writtenPaths = if(writtenQual is ValueQualifier.CleanedValue && getPaths(c.value as TACSymbol.Var, whole = whole).size == 1) {
            // We may see
            // Y := X & MASK
            // Z := Y & MASK
            // (this is the case when a struct field is a contract)
            // so we really want X's paths
            // Q: do we need to make sure MASK is the same (i.e. store it in the qualifier?)
            fun chase(v: TACSymbol.Var): Set<ObjectPath> =
                (postZeroWrite.qualifiers[v] as? ValueQualifier.CleanedValue)?.let {
                    chase(it.cleaned)
                }.takeIf { getPaths(v, whole).size == 1 } ?: getPaths(v, whole)
            chase(writtenQual.cleaned)
        /*
           Again, a boolean value will not have interesting path information. If this boolean value is defined by v != 0, then prefer
            the path of v
         */
        } else if(c.value is TACSymbol.Var && c.value.tag == Tag.Bool && getPaths(c.value, whole = whole).size == 1 && whole.boundsAnalysis[c.value]?.let {
                it as? QualifiedInt
            }?.qual?.any {
                it is IntQualifier.ConditionVar && it.condition == ConditionQualifier.Condition.NEQ && listOf(it.op1, it.op2).any {
                    it == BigInteger.ZERO.asTACSymbol()
                } && listOf(it.op1, it.op2).any {
                    it is TACSymbol.Var
                }
            } == true) {
            whole.boundsAnalysis[c.value]!!.let {
                it as QualifiedInt
            }.qual.filterIsInstance<IntQualifier.ConditionVar>().filter {
                it.condition == ConditionQualifier.Condition.NEQ
            }.filter {
                val l = listOf(it.op1, it.op2)
                l.any {
                    it is TACSymbol.Var
                } && l.any {
                    it == BigInteger.ZERO.asTACSymbol()
                }
            }.firstMapped {
                (it.op1 as? TACSymbol.Var) ?: (it.op2 as? TACSymbol.Var)
            }?.let {
                getPaths(it, whole)
            } ?: return killBaseBuffer
        } else {
            getPaths(c, whole)
        }.let { p ->
            /*
             If q_ is not null that means we are writing into a value that is nested within some dynamic object.
             Thus, the object path associated with the value we are writing will never be a root: it never makes
             sense for the field/element of some struct/array to have an identity that isn't also at least a field/struct.
             */
            if (q_ != null) {
                p.filter {
                    it !is ObjectPathGen.Root
                }.toSet()
            } else {
                p
            }
        }
        /*
        Despite the name, this is a set that holds the objects for which this is a length
         */
        val isLengthWrite = writtenPaths.mapNotNull {
            ((it as? ObjectPathGen.ArrayLength)?.parent as? ObjectPathGen.Root)?.oRoot
        }.toSet()
        val write = WriteValue(
                writtenQual = writtenQual?.takeIf { it !is ValueQualifier.CleanedValue }, // cleaned value is not salient here TODO(jtoman): make an interface?
                writtenPaths = writtenPaths,
                constValue = isConst,
                lengthWriteFor = isLengthWrite,
                symbol = c.value
        )
        /*
        Canonicalize the qualifier.
         */
        val q = if(q_ is ElemPointer && postZeroWrite.qualifiers[q_.parent]?.let {
                    it as? ValueQualifier.OffsetQualifier.DynamicStart
                }?.let {
                    check(it.abiType != null) {
                        "If we have an element pointer to the array ${q_.parent} then we should have resolved it, but don't have an abi type"
                    }
                    it.abiType is LinearizedType.Array && !it.abiType.cont.isDynamic && it.abiType.cont.sizeInArray != EVM_WORD_SIZE
                } == true) {
            ValueQualifier.OffsetQualifier.EncodedFieldPointer(
                    offset = BigInteger.ZERO,
                    parent = q_.parent,
                    indexVars = whole.variablesEqualTo(BigInteger.ZERO)
            )
        } else if(q_ is ValueQualifier.OffsetQualifier.DynamicStart && (q_.sort == DynamicSort.STRUCT || (q_.sort == null && write.lengthWriteFor.isEmpty()))) {
            ValueQualifier.OffsetQualifier.EncodedFieldPointer(
                    offset = BigInteger.ZERO,
                    parent = c.loc,
                    indexVars = setOf()
            )
        } else {
            q_
        }
        /*
         Only one of these is non-null. So first consider the case where we are writing to a root, i.e., a constant index
         */
        return if(rootQual != null) {
            val finder = sigAdjust?.let { sig ->
                elementFinderFor(
                    whole = whole,
                    encoderState = postZeroWrite,
                    sigAdjust = sig
                )
            }
            modelRootWrite(
                whole,
                postZeroWrite,
                write,
                rootQual,
                finder,
                ltacCmd = ltacCmd
            ) ?: killBaseBuffer
        } else {
            /*
              Otherwise, we're writing to an offset qualifier, i.e., a statically unknown, symbolic location
             */
            check(q != null)
            modelSymbolicWrite(
                whole = whole,
                outer = outer,
                m = postZeroWrite,
                write = write,
                q = q,
                buffer = basePointer,
                context = ltacCmd.wrapped
            ) ?: killBaseBuffer
        }
    }

    private fun getPaths(c: TACCmd.Simple.AssigningCmd.ByteStore, whole: PointsToDomain): Set<ObjectPath> {
        val loc = c.value as? TACSymbol.Var ?: return emptySet()
        return getPaths(loc, whole)
    }

    private fun getPaths(
        loc: TACSymbol.Var,
        whole: PointsToDomain
    ): Set<ObjectPath> {
        return decoderAnalysis.getCalldataReadPath(loc, whole).orEmpty() + objectPath.getPathOf(loc, whole)
    }

    /**
     * Find the variables that hold the length of the array being encoded into dynamic start [dyn]
     */
    private fun lengthVarsForEncodedArray(dyn: ValueQualifier.OffsetQualifier.DynamicStart, whole: PointsToDomain) : Set<TACSymbol.Var>? {
        if(dyn.abiType !is LinearizedType.Array || dyn.path !is SerializedPath.Resolved) {
            return null
        }
        return if(dyn.path.o.root is ObjectPathAnalysis.ObjectRoot.CalldataRoot) {
            /*
             If we're at a calldata root, query the decoder state
             */
            whole.decoderState.keysMatching { p, r ->
                r is DecoderAnalysis.AbstractDomain.ReadFrom && decoderAnalysis.getCalldataReadPath(whole = whole, loc = p)?.contains(
                        ObjectPathGen.ArrayLength(dyn.path.o)
                ) == true
            }.toSet()
        } else {
            /*
             Otherwise, query the object path state
             */
            whole.objectPath.keysMatching { _, set ->
                ObjectPathGen.ArrayLength(dyn.path.o) in set
            }.toSet()
        }
    }

    /**
     * As mentioned a great many times so far, objects are resolved lazily.
     * This means that once we resolve a struct, we may conclude that what we thought was an encoded field pointer
     * is actually a next pointer. This abstracts the process for finding this next pointer as follows.
     *
     * [dynamicStruct] is a variable that points to the [analysis.pta.abi.EncoderAnalysis.ValueQualifier.OffsetQualifier.DynamicStart]
     * object that holds the struct. [expectedOffset] is the offset of the [analysis.pta.abi.EncoderAnalysis.ValueQualifier.OffsetQualifier.EncodedFieldPointer]
     * that should be promoted to a next pointer, i.e., the size of the struct pointed to by [expectedOffset].
     *
     * Note that for this search to be sound, [dynamicStruct] must be the "currently" encoding object, i.e. [m].currPointer == [dynamicStruct].
     *
     * If a variable that is a suitable candidate for promoting to a next pointer is found, then [f] is called with that variable
     * as a non-null argument. If the search fails (because [dynamicStruct] is not the most recent encoded object, or the
     * variable simply doesn't exist) then [f] is called with null.
     */
    private fun <T> findNextPointer(
            m: EncodingState,
            qual: TreapMap<TACSymbol.Var, ValueQualifier>,
            expectedOffset: BigInteger,
            dynamicStruct: TACSymbol.Var,
            f: (TACSymbol.Var?) -> T
    ) : T? {
        var curr : TACSymbol.Var? = null
        if(m.currPointer != dynamicStruct) {
            return f(null)
        }
        for((k, v) in qual) {
            val efp = v as? ValueQualifier.OffsetQualifier.EncodedFieldPointer ?: continue
            if(efp.parent != dynamicStruct) {
                continue
            }
            if(efp.offset == expectedOffset) {
                if (curr != null) {
                    return null
                }
                curr = k
            } else if(efp.offset > expectedOffset) {
                return null
            }
        }
        return f(curr)
    }

    private fun modelSymbolicWrite(
            whole: PointsToDomain,
            outer: State,
            m: EncodingState,
            write: WriteValue,
            q: ValueQualifier.OffsetQualifier,
            buffer: WritablePointer,
            context: LTACCmd
    ) : EncodingState? {
        unused(outer)
        unused(buffer)
        /*
         The only time we reason about writes directly to the dynamic start is if we have an array (or unresolved)
         and a write of a length. Otherwise we should be dealing with an ElemPointer or an EFP
         */
        ptaInvariant(q !is ValueQualifier.OffsetQualifier.DynamicStart ||
                ((q.sort == null || q.sort == DynamicSort.ARRAY) && write.lengthWriteFor.isNotEmpty())) {
            "Writing a non-length to the beginning of a dynamic start for an array."
        }
        fun ValueQualifier.OffsetQualifier.closestParent() : ValueQualifier.OffsetQualifier.DynamicStart = when(this) {
            is ValueQualifier.OffsetQualifier.DynamicStart -> this
            is ValueQualifier.OffsetQualifier.ArrayElemStart -> m.qualifiers[this.parent] as ValueQualifier.OffsetQualifier.DynamicStart
            is ValueQualifier.OffsetQualifier.ArrayElem -> m.qualifiers[this.parent] as ValueQualifier.OffsetQualifier.DynamicStart
            is ValueQualifier.OffsetQualifier.EncodedFieldPointer ->
                m.qualifiers[this.parent] as ValueQualifier.OffsetQualifier.DynamicStart
            is ValueQualifier.OffsetQualifier.DynamicStridePointer -> m.qualifiers[this.parent] as ValueQualifier.OffsetQualifier.DynamicStart
        }
        /*
          No paths case
         */
        if(write.writtenPaths.isEmpty() || write.writtenQual != null) {
            ptaInvariant(write.lengthWriteFor.isEmpty()) {
                "Have no access paths, but do have length write information for $write"
            }
            /* we assume that dynamic writes are performed recursively.
               Thus, a write to a tuple of dynamic values must have been resolved in the first iteration of this
               loop. That gives the invariant:
             */

            val parent = q.closestParent()
            ptaInvariant(q !is ValueQualifier.OffsetQualifier.DynamicStridePointer || parent.abiType != null) {
                "Expected any dynamism to be resolved in a single iteration of the loop"
            }
            if(parent.sort == DynamicSort.ARRAY) {
                if(q is ValueQualifier.OffsetQualifier.DynamicStart) {
                    // cannot write a non-path value into the length segment of an encoded array
                    return null.andDebug<EncodingState?> {
                        "Tried to write non-path into start of array @ $q"
                    }
                }
                /*
                  We expect that before writing anything into the array element segment, we would
                  have resolved the array's paths, and thus its type
                 */
                ptaInvariant(parent.abiType is LinearizedType.Array) {
                    "$parent has sort ARRAY but type is ${parent.abiType}"
                }
                // cannot write random values (qualified or not) into dynamic portions
                if(!parent.abiType.cont.isDynamic) {
                    return null.andDebug<EncodingState?> {
                        "Writing junk into non-dynamic elements of $parent @ $write"
                    }
                }
                /*
                  We can't be an encoded field or a stride field,
                  because that would imply that there is some internal structure to the array elements (i.e., a tuple
                  of integers, or a non-dynamic struct) in which case we would expect to see some path information.
                 */
                if(q !is ElemPointer) {
                    return null.andDebug<EncodingState?> {
                        "Writing an expected dynamic offset into an array, but the location wasn't a direct field"
                    }
                }
                if(write.writtenQual is ValueQualifier.OffsetPointerFor) {
                    if(write.writtenQual.parent != q.parent) {
                        return null.andDebug<EncodingState?> {
                            "Dynamic offset is for a different dynamic object $write != ${q.parent}"
                        }
                    }
                    ptaInvariant(m.nextPointer != null) {
                        "Have offset for next location, but the next pointer is null"
                    }
                    return m.transitionCurr(m.nextPointer).copy(
                            qualifiers = m.qualifiers + (m.nextPointer to dynamicFromBlock(
                            parent = parent,
                            writeLoc = OffsetLocation.Elem
                        ))
                    )
                } else {
                    val d = m.nextPointer?.let { nxt ->
                        val base = extractBase(q.parent, m) ?: return@let null
                        matchAdditionToWrite(
                                inv = whole.invariants,
                                nextPointer = nxt,
                                writeLoc = OffsetLocation.Elem,
                                writeValue = write.symbol,
                                m = m,
                                dyn = base
                        )?.clearLastWrittenOffset(q.parent)
                    }
                    if(d != null) {
                        return d
                    }
                    if(parent.lastWrittenOffset != null) {
                        return null.andDebug<EncodingState?> {
                            "Last written offset of $parent is not null"
                        }
                    }
                    check(m.qualifiers[q.parent] == parent)
                    /*
                     record that we last saw a write of an offset, and so we expect to see a computation of the next pointer soon
                     */
                    return m.copy(
                            qualifiers = m.qualifiers + (q.parent to parent.copy(
                                    lastWrittenOffset = OffsetWrite(
                                            offset = write.symbol,
                                            where = OffsetLocation.Elem
                                    )
                            ))
                    ).expectNext()
                }
            } else {
                check(parent.sort == null || parent.sort == DynamicSort.STRUCT)
                check(q is ValueQualifier.OffsetQualifier.EncodedFieldPointer || q is ValueQualifier.OffsetQualifier.DynamicStridePointer)
                val ty = parent.abiType
                val (parentVar, writeLocation) = if(q is ValueQualifier.OffsetQualifier.DynamicStridePointer) {
                    check(ty != null && ty is LinearizedType.Struct)
                    /*
                      Striding over dynamic types is weird. Basically, if we ever have a tuple of any dynamic type, the stride must occur
                      within its own contained, dynamic block. This is the basis of these checks
                     */
                    if(q.stridePath.root != BigInteger.ZERO || q.strideBy != EVM_WORD_SIZE || q.innerOffset != BigInteger.ZERO || q.stridePath.path.isNotEmpty()) {
                        return null.andDebug<EncodingState?> {
                            "Invalid striding for apparently dynamic contents at $q"
                        }
                    }
                    /*
                      Check that this is indeed a tuple-able, dynamic object
                     */
                    ty.offset.values.monadicFold { a, b ->
                        a.takeIf { it.equivModuloPath(b) }?.takeIf { it.isDynamic }
                    } ?: return null.andDebug<EncodingState?> { "Fields of $ty strided by $q are not tuple safe" }
                    // then this is fine
                    q.parent to OffsetLocation.StaticArray
                } else {
                    check(q is ValueQualifier.OffsetQualifier.EncodedFieldPointer)
                    if(ty != null) {
                        check(ty is LinearizedType.Struct)
                        if(ty.offset[q.offset]?.isDynamic != true) {
                            return null.andDebug<EncodingState?> {
                                "Attempting to write an offset in known type at $q in $ty when that is not dynamic"
                            }
                        }
                    }
                    q.parent to OffsetLocation.Field(q.offset)
                }
                ptaInvariant(ty == null || ty is LinearizedType.Struct) {
                    "The parent of the write $write is resolved to a non-struct type: $ty"
                }
                /*
                  We are writing an offset
                 */
                if(write.writtenQual is ValueQualifier.OffsetPointerFor) {
                    if(write.writtenQual.parent != parentVar) {
                        return null.andDebug<EncodingState?> {
                            "Parent for offset does not mathc: ${write.writtenQual} != $parentVar"
                        }
                    }
                    ptaInvariant(m.nextPointer != null) {
                        "Have offset qualifier at write $write, but no known next pointer"
                    }
                    return m.copy(
                            qualifiers = m.qualifiers + (m.nextPointer to dynamicFromBlock(
                                    parent = parent,
                                    writeLoc = writeLocation
                            ))
                    ).transitionCurr(m.nextPointer)
                } else {
                    val writeSymbol = if(write.constValue != null) {
                        write.constValue.asTACSymbol()
                    } else {
                        write.symbol
                    }
                    /*
                        If we have a next pointer, and adding this constant to the beginning of this object
                        reaches the free pointer, go ham
                     */
                    if(m.nextPointer != null) {
                        val d = matchAdditionToWrite(
                                inv = whole.invariants,
                                nextPointer = m.nextPointer,
                                m = m,
                                writeValue = writeSymbol,
                                dyn = extractBase(parentVar, m)!!,
                                writeLoc = writeLocation
                        )?.clearLastWrittenOffset(parentVar)
                        if(d != null) {
                            return d
                        }
                    }
                    if(write.constValue != null) {
                        /*
                          Or perhaps this is a constant value that corresponds to an extant EncodedFieldPointer,
                          in which case we promote that field pointer to a dynamic child at the location given by writeLocation.
                         */
                        val d = findNextPointer(
                                m,
                                m.qualifiers,
                                expectedOffset = write.constValue,
                                dynamicStruct = parentVar
                        ) { v ->
                            if(v == null) {
                                null
                            } else {
                                m.copy(
                                        qualifiers = m.qualifiers + (v to dynamicFromBlock(
                                                writeLoc = writeLocation,
                                                parent = parent
                                        ))
                                ).transitionCurr(v)
                            }
                        }
                        if(d != null) {
                            return d
                        }
                    }
                    /*
                      Otherwise, record the value we wrote (and where) and hope to see it computed shortly.
                     */
                    return m.copy(
                            qualifiers = m.qualifiers + (parentVar to parent.copy(
                                    lastWrittenOffset = OffsetWrite(
                                            where = writeLocation,
                                            offset = writeSymbol
                                    )
                            ))
                    ).expectNext()
                }
            }
        } else if(write.lengthWriteFor.isNotEmpty()) {
            if(q !is ValueQualifier.OffsetQualifier.DynamicStart) {
                return null.andDebug<EncodingState?> {
                    "Write of length ${write.lengthWriteFor} to a non-dynamic start: $q"
                }
            }
            /*
             Then we have already resolved this array, and so we simply check if the paths match up the way
             we expect.
             */
            if(q.sort == DynamicSort.ARRAY) {
                check(q.abiType is LinearizedType.Array || q.abiType is LinearizedType.EmptyArray)
                check(q.abiType != null)
                if(ObjectPathGen.ArrayLength(q.abiType.path) !in write.writtenPaths) {
                    return null.andDebug<EncodingState?> {
                        "Array paths do not match: ${q.abiType.path} vs ${write.writtenPaths}"
                    }
                }
                return m
            } else if(q.sort == DynamicSort.STRUCT) {
                return null.andDebug<EncodingState?> {
                    "Have write of lengths ${write.writtenPaths} into struct $q"
                }
            } else {
                // we can resolve this!
                check(q.path is Unresolved)
                val paths = write.writtenPaths.mapNotNull {
                    (it as? ObjectPathGen.ArrayLength)?.parent
                }
                return doPathMatching(paths, whole, q.path, m, context)
            }
        } else {
            check(write.writtenPaths.isNotEmpty())
            /*
              Basically, we expect that if we're writing a value, it must always be a field of something, or an element.
              The only time that is not the case is if we are writing a length into a dynamic start, which is handled up above.
             */
            ptaInvariant(q !is ValueQualifier.OffsetQualifier.DynamicStart) {
                "Writing paths @ $write, but didn't have offsets generated for us"
            }
            val parent = q.closestParent()
            if(parent.sort == DynamicSort.ARRAY) {
                check(parent.abiType is LinearizedType.Array)
                /*
                 Compute the path we expect to be writing here (based on the "shape" of where we are writing
                 and our parent) and then check for consistency between paths.
                 */
                val expectedPath = if(q is ElemPointer) {
                    ObjectPathGen.ArrayElem(parent.abiType.path)
                } else if(q is ValueQualifier.OffsetQualifier.EncodedFieldPointer) {
                    check(parent.abiType.cont is LinearizedType.Struct) {
                        "$write => $parent"
                    }
                    parent.abiType.cont.offset[q.offset]!!.path
                } else {
                    check(q is ValueQualifier.OffsetQualifier.DynamicStridePointer && parent.abiType.cont is LinearizedType.Struct)
                    parent.abiType.cont.toStaticArrayPath(q.toFullPath()) ?: return null
                }
                return if(write.writtenPaths.none {
                            it.joinOrNull(expectedPath) != null
                        }) {
                    null
                } else {
                    m
                }
            } else if(parent.abiType == null) {
                /*
                  We can resolve!
                 */
                check(q is ValueQualifier.OffsetQualifier.EncodedFieldPointer)
                check(parent.path is Unresolved)
                /**
                 * Find the path that corresponds to this dynamic location.
                 * Namely, find the (single) path whose root is a type that,
                 * after traversing `parent.fields` object fields yields a struct
                 * where the path at the offset of our write location (i.e. q.offset)
                 * is exactly the path being written.
                 */
                val resolved = write.writtenPaths.mapNotNull { path ->
                    getABILayoutOfType(path.root, whole)?.takeIf {
                        parent.path.fields.monadicFold(it) { Curr, f ->
                            (Curr as? LinearizedType.Struct)?.offset?.get(f)?.takeIf {
                                it.isDynamic
                            }
                        }?.let {
                            it as? LinearizedType.Struct
                        }?.offset?.get(q.offset)?.path == path
                    }
                }.let { cand ->
                    if(cand.size == 1) {
                        return@let cand
                    }
                    // we have ambiguous possibilities. Multiple dynamic types could give us this path
                    // try to (heuristically) resolve this ambiguity by looking for the largest EFP that
                    // whose offset equals the total size of the candidate type: this suggests that value
                    // is intended to be the next pointer
                    m.qualifiers.values.mapNotNull { vq ->
                        (vq as? ValueQualifier.OffsetQualifier.EncodedFieldPointer)?.takeIf {
                            it.parent == q.parent
                        }?.offset
                    }.maxOrNull()?.let { largestOffs ->
                        cand.singleOrNull {
                            (it as? LinearizedType.Struct)?.totalEncodedSize() == largestOffs
                        }?.let(::listOf)
                    }.also { r ->
                        if(r == null) {
                            logger.warn {
                                "At $context, couldn't resolve multiple possible dynamic object candidates: $cand"
                            }
                        }
                    } ?: cand
                }.singleOrNull() ?: return null
                val rootStride = m.rootStrides.builder()
                val rootState = m.varRoots.builder()
                val qual = m.qualifiers.builder()
                if(!updatePointers(
                        elemFinder = null,
                        abi = resolved,
                        qualifiers = qual,
                        rootStrides = rootStride,
                        bufferState = rootState,
                        unresolved = parent.path,
                        context = context
                )) {
                    return null
                }
                ptaInvariant(resolved is LinearizedType.Struct) {
                    "We fully expect to have resolved ${q.parent} to s struct, instead we have $resolved"
                }
                return findNextPointer(
                        m,
                        qual = qual.build(),
                        dynamicStruct = q.parent,
                        expectedOffset = resolved.offset.size.toBigInteger() * EVM_WORD_SIZE
                ) { v ->
                    /*
                      If we didn't find a next pointer, no big deal, keep the updates computed in updatePointers
                     */
                    if(v == null) {
                        m.copy(
                                qualifiers = qual.build(),
                                varRoots = rootState.build(),
                                rootStrides = rootStride.build()
                        )
                    } else {
                        /*
                          Otherwise update the nextPointer as appropriate
                         */
                        qual.remove(v)
                        m.copy(
                                qualifiers = qual.build(),
                                varRoots = rootState.build(),
                                rootStrides = rootStride.build()
                        ).transitionNext(v)
                    }
                }
            } else {
                ptaInvariant(parent.abiType is LinearizedType.Struct && (q is ValueQualifier.OffsetQualifier.EncodedFieldPointer || q is ValueQualifier.OffsetQualifier.DynamicStridePointer)) {
                    "Resolved type is non-null, not an array, but isn't a struct ${parent.abiType}"
                }
                /*
                 Otherwise get the expect path based on the resolved paths
                 */
                val path = if(q is ValueQualifier.OffsetQualifier.EncodedFieldPointer) {
                    parent.abiType.offset[q.offset]?.path ?: return null
                } else {
                    check(q is ValueQualifier.OffsetQualifier.DynamicStridePointer)
                    parent.abiType.toStaticArrayPath(q.toFullPath()) ?: return null
                }
                /*
                 And then check consistency
                 */
                if(write.writtenPaths.all {
                            it.joinOrNull(path) == null
                        }) {
                    return null
                }
                return m
            }
        }
    }

    private fun getABILayoutOfType(v: ObjectPathAnalysis.ObjectRoot, whole: PointsToDomain) : LinearizedType? {
        return when(v) {
            is ObjectPathAnalysis.ObjectRoot.V -> getABILayoutOfType(
                ObjectPathGen.Root(v), heapType = pointerSem.getHeapType(
                    v.v, pState = whole
            ) ?: return null)
            is ObjectPathAnalysis.ObjectRoot.CalldataRoot -> {
                getABILayoutOfType(ObjectPathGen.Root(v), decoderAnalysis.getCalldataRootType(v) ?: return null)
            }
        }
    }

    /**
     * A type [heapType] that begins at [root], compute its [LinearizedType] representation. The [LinearizedType] representation
     * is a tree like representation, that has several handy properties:
     * 1. Each [LinearizedType] is associated with an [ObjectPath] that gives the identity of the value with that type
     * 2. The [LinearizedType] representation flattens non-dynamic structs as required by the ABI spec.
     *
     * Ultimately, the [LinearizedType] lets us know at which offsets within an object which object paths are supposed to appear.
     * This is non-trivial because of the flattening required by the ABI spec, offset 96 in the encoding
     * of a struct s may not be the third field of s, depending on whether the first two fields are non-dynamic types
     * that have been flattened.
     */
    private fun getABILayoutOfType(root: ObjectPath, heapType: HeapType): LinearizedType? {
        return when(heapType) {
            HeapType.Int -> LinearizedType.Word(root)
            is HeapType.OffsetMap -> {
                var it = BigInteger.ZERO
                val output = mutableMapOf<BigInteger, LinearizedType>()
                heapType.fieldTypes.entries.sortedBy { it.key }.forEach { (k,v) ->
                    val subTy = getABILayoutOfType(
                        ObjectPathGen.Field(
                            offset = k,
                            parent = root
                    ), v) ?: return null
                    if(!subTy.isDynamic && subTy is LinearizedType.Struct) {
                        subTy.offset.forEach { t, u ->
                            output[t + it] = u
                        }
                    } else {
                        output[it] = subTy
                    }
                    it += subTy.sizeInArray
                }
                LinearizedType.Struct(
                        output,
                        path = root
                )
            }
            HeapType.ByteArray -> LinearizedType.Array(
                    isByte = true,
                    path = root,
                    cont = LinearizedType.Word(
                            path = ObjectPathGen.ArrayElem(root)
                    )
            )
            is HeapType.Array -> LinearizedType.Array(
                    isByte = false,
                    path = root,
                    cont = getABILayoutOfType(
                            root = ObjectPathGen.ArrayElem(root),
                            heapType = heapType.elementType
                    ) ?: return null
            )
            HeapType.EmptyArray -> LinearizedType.EmptyArray(path = root)
            is HeapType.TVar -> heapType.ty.ifResolved(
                    intChoice = LinearizedType.Word(path = root),
                    ptrChoice = LinearizedType.EmptyArray(path = root)
            ) ?: heapType.ty.expectPointer(LinearizedType.EmptyArray(path = root))
        }
    }

    private fun doPathMatching(
        paths: List<ObjectPath>,
        whole: PointsToDomain,
        path: Unresolved,
        m: EncodingState,
        context: LTACCmd
    ): EncodingState? {
        val chosenRootType = paths.mapNotNull {
            val abi = getABILayoutOfType(it.root, whole = whole) ?: return@mapNotNull null
            if (checkPathConsistency(abi, solution = path, p = it)) {
                abi
            } else {
                null
            }
        }.singleOrNull() ?: return null
        val roots = m.varRoots.builder()
        val strideRoots = m.rootStrides.builder()
        val qual = m.qualifiers.builder()
        val succ = updatePointers(
            elemFinder = null,
            bufferState = roots,
            qualifiers = qual,
            unresolved = path,
            rootStrides = strideRoots,
            abi = chosenRootType,
            context = context
        )
        if (!succ) {
            return null
        }
        return m.copy(
                qualifiers = qual.build(),
                varRoots = roots.build(),
                rootStrides = strideRoots.build()
        )
    }

    /**
     * Given a struct and a stridepath within that struct, compute the static array paths. Roughly,
     * whereever [p] has a strideloop, we expect to see a StaticArrayElem in the path, and wherever we see
     * a ConstStep we expect to see a Field.
     *
     * We do this by recursively visiting every location in the struct that is "touched" by the stride path,
     * and iteratively joining (i.e., weakening) the path, introducing StaticArrayElems as necessary.
     */
    private fun LinearizedType.Struct.toStaticArrayPath(p: StridePath) : ObjectPath? {
        val maxSize = this.offset.size.toBigInteger() * EVM_WORD_SIZE
        if(p.root >= maxSize) {
            return null
        }
        val stridingStart = p.path.toFirstElem(p.root)
        if(stridingStart >= maxSize) {
            return null
        }
        /*
          We seed the joining process described above with the path of the first location touched by the path,
          i.e., the location reached by iterating all loops 0 times
         */
        ptaInvariant(p.path.isEmpty() || p.path.any {
            it is StrideStep.StrideLoop
        }) {
            "Trivial path in stride $p"
        }
        return checkFrom(0, p.root, p.path, this.offset[stridingStart]?.path ?: return null)
    }

    private fun LinearizedType.Struct.totalEncodedSize(): BigInteger = offset.size.toBigInteger().times(EVM_WORD_SIZE)

    private fun LinearizedType.Struct.checkFrom(
        ind: Int,
        start: BigInteger,
        remaining: List<StrideStep>,
        accum: ObjectPath
    ) : ObjectPath? {
        /*
          Base case: we have finished, start is one of the locations touched by this path, join
          it with our accumulator
         */
        if(ind == remaining.size) {
            return this.offset[start]?.path?.joinOrNull(accum)
        }
        val l = remaining[ind]
        return if(l is StrideStep.ConstStep) {
            /*
              Easy case, increment our current position (in start)
             */
            checkFrom(ind + 1, start + l.c, remaining, accum)
        } else {
            check(l is StrideStep.StrideLoop)
            /*
              Find the first element visited from our starting location (start)
              by taking all REMAINING loops zero times (using the toFirstElem function).
             */
            val firstChild = if(ind == remaining.lastIndex) {
                start
            } else {
                remaining.subList(ind + 1, remaining.lastIndex).toFirstElem(start)
            }
            /*
              nxt is the first child of the "next" element in our loop. (we can add directly to
              firstChild here because the toFirstElem process commutes with adding to the start)
             */
            val nxt = firstChild + l.c
            /*
              Find the greatest common parent, this is the path of the type that "contains" this static stride,
              i.e., the path of the static array being strided over at this level.
             */
            val gcp = this.offset[firstChild]?.path?.gcp(
                    this.offset[nxt]?.path ?: return null
            ) ?: return null
            var childIt = start
            var accumIt = accum
            /*
             * Iterate through the fields of this struct, provided the iteration doesn't "hit" another parent
             * path.
             * For example, suppose we have:
             * struct Foo {
             *    uint b;
             *    Bar[3] gorp;
             *    uint w;
             *    uint x;
             *    uint y;
             *    uint z;
             * }
             * struct Bar {
             *    uint a;
             *    uint[3] baz;
             * }
             *
             * And the stride path is : (root=32).(loop 128).(offset 32)
             * This will be flattened into a single struct, whose fields are:
             * 0: foo.b
             * 32: foo.gorp[0].a
             * 64: foo.gorp[0].baz[0]
             * ...
             * 128: foo.gorp[0].baz[2]
             * 160: foo.gorp[1].a
             * 192: foo.gorp[1].baz[0]
             * ...
             * 416: foo.w
             * 448: foo.x
             * 480: foo.y
             * 512: foo.z
             * When we reach the first (loop 128) start will be 32 (because that is our root), and the first
             * child will be 64, aka foo.gorp[0].baz[0]
             *
             * The next child will be 64 + 128, aka foo.gorp[1].baz[0]. The greatest common parent here is
             * foo.gorp[1]. We then iterate, starting from 32 stepping 128 at a time, and then recursing, where at each
             * recursive call we will step another 32 bytes. During this process we will touch foo.gorp[0].baz[0], foo.gorp[1].baz[0],
             * and foo.gorp[2].baz[0]. Note that when we hit 416, the loop terminates, foo.w does not have foo.gorp as a prefix.
             *
             * At the end of this process, we will the object path foo.gorp[*].baz[0], i.e., the first element of the baz field
             * of each element of foo.gorp.
             *
             * Let us consider another example, this time with (root=32).(loop 128).(offset 32).(loop 32). Then as in the outer
             * case we will recurse after stepping 128 bytes at a time, starting the recursive checkFrom calls at 32, 160, 288, and
             * 416. Let us consider the case where childIt = 160 when we recurse. Then we will step 32 bytes (giving an
             * offset of 192), and then hit the second loop. In this case, firstChild and next are foo.gorp[1].baz[0]
             * and foo.gorp[1].baz[1] whose greatest  common parent is foo.gorp[1].baz. Thus, when start from 192,
             * iterating 32 bytes at a time, we will stop when we would hit foo.gorp[2].a, because it doesn't have
             * foo.gorp[1].baz.
             *
             * TL;DR - this lets us take a stride path within a struct and extract out the ObjectPath (with StaticElem
             * steps) it represents.
             */
            while(childIt < (this.offset.size.toBigInteger() * EVM_WORD_SIZE) && this.offset[childIt]?.path?.hasPrefix(gcp) == true) {
                accumIt = checkFrom(ind + 1, childIt, remaining, accumIt) ?: return null
                childIt += l.c
            }
            accumIt
        }
    }

    /**
     * Does [this] have [other] as a prefix. A prefix ONLY includes object fields
     */
    private fun ObjectPath.hasPrefix(other: ObjectPath) : Boolean {
        if(this == other) {
            return true
        }
        return when(this) {
            is ObjectPathGen.Root -> false
            is ObjectPathGen.Field -> this.parent.hasPrefix(other)
            is ObjectPathGen.StaticArrayField -> false
            is ObjectPathGen.ArrayElem -> false
            is ObjectPathGen.ArrayLength -> false
        }
    }

    private fun ObjectPath.gcp(other: ObjectPath) : ObjectPath? {
        return if(this == other) {
            this
        } else if(this !is ObjectPathGen.Field || other !is ObjectPathGen.Field) {
            null
        } else {
            this.parent.gcp(other.parent)
        }
    }


    private fun modelRootWrite(
            whole: PointsToDomain,
            m: EncodingState,
            write: WriteValue,
            rootField: ValueQualifier.RootQualifier,
            elementFinder: ElementFinder?,
            ltacCmd: LTACCmdView<TACCmd.Simple.AssigningCmd.ByteStore>
    ) : EncodingState? {
        /* We are writing a length into a root field. This means we can resolve the dynamic object */
        if(write.writtenQual == null && write.lengthWriteFor.isNotEmpty()) {
            ptaInvariant(write.writtenPaths.all {
                it is ObjectPathGen.ArrayLength ||
                        (it is ObjectPathGen.Root && it.oRoot is ObjectPathAnalysis.ObjectRoot.V && it.oRoot.v == write.symbol)
            }) {
                "Numeric analysis thinks ${write.symbol} @ $ltacCmd is an array length, but the path analysis disagrees: ${write.writtenPaths}"
            }
            ptaInvariant(m.nextPointer == null && m.currPointer == null) {
                "We are writing a dynamic length into root location @ $write, but have already bootstrapped ${m.nextPointer} ${m.currPointer}"
            }
            ptaInvariant(write.writtenPaths.isNotEmpty()) {
                "Have writing a length ${write.lengthWriteFor} but object analysis disagrees: ${write.writtenPaths}"
            }
            ptaInvariant(rootField is ValueQualifier.RootQualifier.RootFieldPointer) {
                "Have unresolved tuple that contains dynamic, but didn't resolve it on the first iteration?"
            }
            /*
              Find plausible "guesses" for where dynamic objects start, and their nesting relationship.
              For example, given
                value: 32 | 64 | 32 | TARGET
                index: 0  | 32 | 64 | 96
              There are two possible paths. the first assumes that 32 @ index 0 is an offset to a dynamic
              object (which starts at index 32), the first field of which is also an offset that gives
              a dynamic object that starts at 96 (which is where we are writing the length).

              The other possibility is that the first 32 is just a random constant, and 64 is an offset to a dynamic
              object (which starts at 64), whose first field is an offset that gives 96 as a dynamic start.

              Which is right? We don't know! We can try to deduce it based on the object paths of the length field we
              are writing, but if we get really unlucky the encoder will actually just fail here. However, our hope is that
              abi.encodes and calls with exactly the right combination of multiples of 32 to confuse the encoder analysis are
              just going to be so unlikely.
             */
            val solutions = findPaths(m = m.varRoots, targetOffset = rootField.offset)
            if(solutions.isEmpty()) {
                return null.andInfo {
                    "Could not find a consistent path through known constant writes @ $ltacCmd"
                }
            }
            /*  Each solution is an unresolved path, i.e., a root and a series of field dereferences.
                So in our example above, the first solution would be Uresolved(32, [0]) and
                the second solution would be Unresolved(64, [0]), on both cases, after starting from the
                given root, we follow the offset of the first field to give the location we are writing to.
             */
            val selection = solutions.flatMap { sol ->
                /*
                 For each solution, out if the type of the root object being written is consistent with
                 the field information contained in the solution.

                 There may be multiple possible lengths (because the array we are encoding has been nested
                 deeply within some struct, so we have to try all combos)
                 */
                write.writtenPaths.mapNotNull { p ->
                    if(p !is ObjectPathGen.ArrayLength) {
                        return@mapNotNull null
                    }
                    val t = p.parent
                    val abi = getABILayoutOfType(p.root, whole) ?: return@mapNotNull null
                    if(!checkPathConsistency(abi, sol, t)) {
                        return@mapNotNull null
                    } else {
                        /*
                          Then the solution sol we found has a root with ABI type abi, where following the fields
                          in the solution yields one of the paths for the array whose length we are writing.

                          That is, we have "guessed" that the root is of type abi, and the object path of the
                          array we are encoding is t.
                         */
                        sol to ResolvedPath(t, abi)
                    }
                }
            }
            /*
              Ambiguous, give up
             */
            if(selection.size != 1) {
                return null.andInfo {
                    "Could not determine unique path for value being written @ $ltacCmd ($selection)"
                }
            }
            val (urPath, resolution) = selection.single()
            ptaInvariant(resolution.path == resolution.typeAtRoot.derefFields(urPath.fields)?.path) {
                "Solution returned nonsense: path chosen for length write ${resolution.path} doesn't match with root deref ${resolution.typeAtRoot.derefFields(urPath.fields)}"
            }
            val bufferMut = m.varRoots.builder()
            val qualMut = m.qualifiers.builder()
            val rootStrideMut = m.rootStrides.builder()
            /*
              Adjust pointers that we now know are actually DynamicStarts, or EncodedFieldPointers. If this process
              fails, then that means this guess was bad. We don't try another one because that would make this very hard to understand
             */
            if(!updatePointers(
                elemFinder = elementFinder,
                bufferState = bufferMut,
                qualifiers = qualMut,
                unresolved = urPath,
                abi = resolution.typeAtRoot,
                rootStrides = rootStrideMut,
                context = ltacCmd.wrapped
            )) {
                return null.andInfo {
                    "Updating pointers after resolution @ $ltacCmd failed"
                }
            }
            return m.copy(
                    currPointer = ltacCmd.cmd.loc as TACSymbol.Var,
                    qualifiers = qualMut.build(),
                    varRoots = bufferMut.build(),
                    rootStrides = rootStrideMut.build()
            )
        } else if(write.writtenQual == null) {
            /*
              No qualifier, in which case we just record the value we've written (including the path and constant
              information) AS WELL AS the lastRootWrite, in case this turns out to be part of a next pointer computation
              (see internalAdd)
             */
            check(write.lengthWriteFor.isEmpty())
            if(rootField is ValueQualifier.RootQualifier.RootFieldPointer) {
                return m.copy(
                        varRoots = m.varRoots + (rootField.offset to TopLevelWrite(
                            write.writtenPaths,
                            isDefinitelyOffset = false,
                            const = write.constValue,
                            isUnresolvedOffset = false
                        )),
                        lastRootWrite = (write.symbol as? TACSymbol.Var)?.let {
                            RootOffsetWrite(
                                    symbol = it,
                                    logicalField = rootField.offset,
                                    baseVariables = elementFinder?.elementWithIndex(BigInteger.ZERO) ?: emptySet()
                            )
                        }
                )
            } else {
                ptaInvariant(rootField is ValueQualifier.RootQualifier.RootStridePointer) {
                    "Unexpected type hierarchy"
                }
                if(write.writtenPaths.isEmpty()) {
                    return null.andInfo {
                        "No paths in write $write to root stride $rootField @ $ltacCmd"
                    }
                }
                /*
                   We are encoding a top-level static array (or are encoding a static array in an as yet unresolved
                   dynamic struct)
                 */
                return m.copy(rootStrides = m.rootStrides.update(rootField.toFullPath(), treapSetOf()) {
                    it + write.writtenPaths
                })
            }
        } else if(write.writtenQual is ValueQualifier.OffsetForStart) {
            ptaInvariant(m.nextPointer != null) {
                "Have offset but no next pointer @ $write"
            }
            val root = m.varRoots
            ptaInvariant(rootField is ValueQualifier.RootQualifier.RootFieldPointer) {
                "Writing an offset from start to a strided location? Impossible: any striding must occur within its own dynamic object"
            }
            /*
              Find the largest constant that we *know* is an offset. It turns out should only ever be at most
              one of these, and it will give the size of the top level tuple being encoded: the "next pointer"
              for the root tuple is the size of the head portion (in ABI terminology) of the encoded tuple type.
              Thus, any writes of offsets must occur before this constant, i.e., within the top-level tuple.
             */
            val topLevelTupleSize = root.entries.mapNotNull {
                val c = it.value.const?: return@mapNotNull null
                if(!it.value.isDefinitelyOffset) {
                    return@mapNotNull null
                }
                c
            }.maxOrNull() ?: return null.andInfo {
                "Could not infer a maximum tuple size for entries ${root.entries} @ $ltacCmd"
            }
            if(topLevelTupleSize <= rootField.offset) {
                return null.andInfo {
                    "Write of $write to root field $rootField is outside of inferred tuple size @ $ltacCmd"
                }
            }
            return m.copy(
                    qualifiers = m.qualifiers + (m.nextPointer to ValueQualifier.OffsetQualifier.DynamicStart(
                            indexVars = whole.variablesEqualTo(BigInteger.ZERO),
                            lastWrittenOffset = null,
                            path = Unresolved(root = rootField.offset, fields = listOf()),
                            sort = null,
                            abiType = null
                    )),
                    currPointer = m.nextPointer,
                    nextPointer = null,
                    varRoots = m.varRoots + (rootField.offset to TopLevelWrite(
                        const = null,
                        isDefinitelyOffset = true,
                        objectPath = setOf(),
                        isUnresolvedOffset = true
                    ))
            )
        } else {
            return null.andInfo {
                "Write of $write to $rootField is not valid, failing @ $ltacCmd"
            }
        }
    }

    data class ResolvedPath(
        val path: ObjectPath,
        val typeAtRoot: LinearizedType
    )

    /**
     * Updates the qualifier, root state, and root stride state to reflect the resolution of the dynamic object
     * at [unresolved] to have type [abi] at's ROOT (i.e., the type being encoded into the buffer at [unresolved]'s
     * root) value.
     */
    private fun updatePointers(
        elemFinder: ElementFinder?,
        bufferState: MutableMap<BigInteger, TopLevelWrite>,
        qualifiers: MutableMap<TACSymbol.Var, ValueQualifier>,
        unresolved: Unresolved,
        abi: LinearizedType,
        rootStrides: MutableMap<StridePath, TreapSet<ObjectPath>>,
        context: LTACCmd
    ): Boolean {
        val currRoot = bufferState[unresolved.root] ?: throw AnalysisFailureException("Do not have information at root ${unresolved.root}")
        if(currRoot.const != null) {
            /**
             * Then we "retrace" the steps the [findPaths] function took, and discover which indices (i.e., [analysis.pta.abi.EncoderAnalysis.ValueQualifier.RootQualifier.RootFieldPointer]
             * objects) must be promoted to EncodedFieldPointers (or DynamicStarts)
             */
            var dynIt : BigInteger = currRoot.const
            var abiIt = abi
            var i = 0
            while(true) {
                /*
                  The index (in the encoded buffer) where the next child on the path to [unresolved] lies
                 */
                val nextDynIt = if(i <= unresolved.fields.lastIndex) {
                    bufferState[dynIt + unresolved.fields[i]]?.let { b ->
                        ptaInvariant(b.const != null) {
                            "In apparently all-constant path $unresolved at $i we have non-const value $b"
                        }
                        dynIt + b.const
                    }
                } else {
                    null
                }
                if(i <= unresolved.fields.lastIndex) {
                    ptaInvariant(abiIt is LinearizedType.Struct) {
                        "Have a field dereference at $i in ${unresolved.fields}, but current type is not a struct $abiIt"
                    }
                    for((o, ty) in abiIt.offset) {
                        /*
                          buff here is the static index into the encoding buffer that corresponds to the o'th field
                          of the struct abiIt that sits along the path of unresolved to the resolved object.
                         */
                        val buff = o + dynIt
                        /*
                          Check if one of the root strides we have recorded is actually a static array that starts
                           at this field of our (newly resolved) struct.
                         */
                        for((sp, writtenPaths) in rootStrides) {
                            if(sp.root != buff) {
                                continue
                            }
                            val firstChild = abiIt.offset[sp.path.toFirstElem(o)]?.path ?: return false
                            /*
                            using checkFrom, extract the expected static array path expected to be found in rootStrides.
                             */
                            val t = abiIt.checkFrom(ind = 0, start = o, remaining = sp.path, accum = firstChild) ?: return false
                            /*
                             Check that the paths recorded within this stride are all consistent with said path
                             */
                            if(writtenPaths.none {
                                        it.joinOrNull(t) != null
                                    }) {
                                logger.info {
                                    "At field $o in type $abiIt at $dynIt, the paths $writtenPaths for the root stride $sp do no match the expected tuple type $t"
                                }
                                return false
                            }
                        }
                        /*
                          remove strides that match the touched buffer
                         */
                        rootStrides.entries.removeIf {
                            it.key.root ==  buff
                        }
                        val curr = bufferState[buff] ?: continue
                        /*
                          If there is any information recorded at the (static) index for this field of the struct, then:
                          1. If there is constant information, it must be a constant that at the offset along the unresolved path we just resolved (and the type must be dynamic)
                          2. OR, the path information recorded there must be consistent with the path of o
                         */
                        if ((curr.const == null || (abiIt.offset.size.toBigInteger() * EVM_WORD_SIZE) != curr.const || o != unresolved.fields[i] || !ty.isDynamic) && ty.path !in curr.objectPath) {
                            logger.info {
                                "$curr at field $o (type $ty) in type $abiIt does not have valid path information and is not a valid dynamic offset"
                            }
                            return false
                        }
                        // it is consistent, and we don't need to track it anymore
                        bufferState.remove(buff)
                    }
                }
                if(elemFinder != null) {
                    /*
                      We know that every index visited along the unresolved path must be a dynamic start,
                      and it must be resolved to the intermediate abi type (stored in abiIt).
                     */
                    val baseDyn = elemFinder.elementWithIndex(dynIt)
                    baseDyn.forEach {
                        qualifiers[it] = ValueQualifier.OffsetQualifier.DynamicStart(
                            abiType = abiIt,
                            sort = abiIt.toSort()!!,
                            path = SerializedPath.Resolved(abiIt.path),
                            indexVars = setOf(),
                            lastWrittenOffset = null
                        )
                    }
                    /*
                     What if there are multiple baseDyn? This is bad for structs, because it makes detecting static
                     strides HARD!
                     */
                    if(abiIt is LinearizedType.Struct) {
                        /*
                        so...try to heuristically find the "true" dynamic start, i.e., the variable for which the other ones are copies
                        (and therefore a field pointer at offset 0). The heuristic: if one dynamic start is the source
                        of for all other definitions.

                        This is gross!!
                         */
                        val completeInfo by lazy {
                            baseDyn.associateWith { parent ->
                                baseDyn.all { copyOf ->
                                    copyOf == parent || graph.cache.def.defSitesOf(copyOf, context.ptr).any {
                                        // Detect copy := parent + 0
                                        graph.elab(it)
                                            .maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.cmd?.rhs?.let { rhs ->
                                            parent in rhs.getFreeVars() &&
                                                LogicalEquivalence.equiv(
                                                    parent.asSym(), rhs
                                                )
                                        } == true
                                    }
                                }
                            }
                        }

                        val singletonParent = baseDyn.singleOrNull { parent ->
                            baseDyn.all { copyOf ->
                                copyOf == parent || graph.cache.def.defSitesOf(copyOf, context.ptr).any {
                                    graph.elab(it).maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.cmd?.rhs?.let { rhs ->
                                        parent in rhs.getFreeVars() &&
                                        LogicalEquivalence.equiv(
                                            parent.asSym(), rhs
                                        )
                                    } == true
                                }
                            }
                        } ?: return false.andInfo {
                            "Could not find unique start for possible struct pointer $baseDyn at $context. Complete info: $completeInfo"
                        }
                        for(o in abiIt.offset.keys) {
                            /*
                              Find existing RootFieldPointers (or unqualified pointers, but there shouldn't be any????)
                              that correspond to encoded field pointers of this struct.
                             */
                            val toEncodedFields = elemFinder.elementWithIndex(dynIt + o)
                            for(v in toEncodedFields) {
                                if(singletonParent == v) {
                                    continue
                                }
                                qualifiers[v] = ValueQualifier.OffsetQualifier.EncodedFieldPointer(
                                        offset = o,
                                        indexVars = setOf(),
                                        parent = singletonParent
                                )
                            }
                        }
                    } else if(abiIt is LinearizedType.Array) {
                        elemFinder.elementWithIndex(dynIt + EVM_WORD_SIZE).forEach {
                            qualifiers[it] = ValueQualifier.OffsetQualifier.ArrayElemStart(
                                parent = baseDyn.singleOrNull()  ?: return@forEach,
                                indexVar = setOf()
                            )
                        }
                    }
                }
                /*
                 The last field must be traversed, and then THAT resulting index must be processed, hence the
                 strange loop format.
                 */
                if(i <= unresolved.fields.lastIndex) {
                    /*
                      Why would we have a null nextDynIt? Once we have encoded at least
                      one dynamic object, all future dynamic objects MUST have non-constant value in the root.
                      Won't that mean we skip all of the above consistency checking? Yes, but that's not a problem,
                      because after the first dynamic object is encoded, all future writes that are part of a dynamic
                      object's encoding will be properly classified as such, and we won't have to do this post-hoc cleanup.
                     */
                    if(nextDynIt == null) {
                        break
                    }
                    check(abiIt is LinearizedType.Struct)
                    dynIt = nextDynIt
                    abiIt = abiIt.offset[unresolved.fields[i]]!!
                    i++
                } else {
                    break
                }
            }
        }
        for(it in qualifiers.entries) {
            val (_,v) = it
            /*
              But once we HAVE gotten the ball rolling with our first encoding, this means
              we have to explicitly search out DynamicStart objects that are known to be part of a dynamic object
              encoding, but for which we don't yet have path information. Here we update these the dynamic objects
              have the newly resolved paths...
             */
            if(v !is ValueQualifier.OffsetQualifier.DynamicStart) {
                continue
            }
            if(v.path !is Unresolved) {
                continue
            }
            check(v.abiType == null)
            if(v.path.root != unresolved.root) {
                continue
            }
            /*
              Each of these pointers is a prefix of the unresolved path
             */
            v.path.fields.forEachIndexed { index, bigInteger ->
                ptaInvariant(unresolved.fields.lastIndex >= index && bigInteger == unresolved.fields[index]) {
                    "Outstanding unresolved dynamic start $v is not a prefix of resolved path $unresolved"
                }
            }
            val parentType = abi.derefFields(v.path.fields) ?: return false.andInfo {
                "Following ${v.path.fields} from type $abi at root ${unresolved.root} failed @ $context"
            }
            check(parentType.isDynamic && (parentType.toSort() == DynamicSort.STRUCT || v.path.fields == unresolved.fields))
            it.setValue(
                    v.copy(
                            path = SerializedPath.Resolved(parentType.path),
                            sort = parentType.toSort()!!,
                            abiType = parentType
                    )
            )
        }
        bufferState[unresolved.root] = bufferState[unresolved.root]!!.copy(
            objectPath = setOf(abi.path),
            isDefinitelyOffset = true,
            isUnresolvedOffset = false
        )
        return true
    }

    private fun checkPathConsistency(abi: LinearizedType, solution: Unresolved, p: ObjectPath): Boolean {
         return abi.derefFields(solution.fields)?.path == p
    }


    sealed class LinearizedType {
        abstract val sizeInArray : BigInteger
        abstract val isDynamic: Boolean
        abstract val path: ObjectPath

        abstract fun equivModuloPath(other: LinearizedType) : Boolean

        data class EmptyArray(override val path: ObjectPath) : LinearizedType() {
            override val isDynamic: Boolean
                get() = true
            override val sizeInArray: BigInteger
                get() = EVM_WORD_SIZE

            override fun equivModuloPath(other: LinearizedType): Boolean {
                return other is EmptyArray || other is Array
            }

            override fun toSort(): DynamicSort = DynamicSort.ARRAY

            override fun staticFieldOf(path: ObjectPath): LinearizedType {
                return this.copy(path = this.path.staticFieldOf(path))
            }
        }

        /**
         * Give the type that exists after dereferencing [fields] in iteration order.
         * If any intermediate type during dereference is not a struct, or the requested field
         * does not exist, the function returns null
         */
        fun derefFields(fields: List<BigInteger>) : LinearizedType? {
            var it = this
            for(f in fields) {
                if(it !is Struct) {
                    return null
                }
                it = it.offset[f] ?: return null
            }
            return it
        }

        data class Array(val cont: LinearizedType, override val path: ObjectPath, val isByte: Boolean) : LinearizedType() {
            override val sizeInArray: BigInteger
                get() = EVM_WORD_SIZE

            override val isDynamic: Boolean
                get() = true

            override fun toSort(): DynamicSort = DynamicSort.ARRAY

            override fun equivModuloPath(other: LinearizedType): Boolean {
                return (other is Array && other.cont.equivModuloPath(this.cont)) || other is EmptyArray
            }

            override fun staticFieldOf(path: ObjectPath): LinearizedType {
                return this.copy(
                        cont = this.cont.staticFieldOf(path),
                        path = this.path.staticFieldOf(path)
                )
            }
        }

        data class Struct(val offset: Map<BigInteger, LinearizedType>, override val path: ObjectPath) : LinearizedType() {
            override val sizeInArray: BigInteger
                get() = if(this.isDynamic) {
                    EVM_WORD_SIZE
                } else {
                    EVM_WORD_SIZE * offset.size.toBigInteger()
                }

            override val isDynamic: Boolean by lazy {
                offset.values.any { it.isDynamic }
            }

            override fun toSort(): DynamicSort = DynamicSort.STRUCT

            override fun equivModuloPath(other: LinearizedType): Boolean {
                return other is Struct && other.offset.keys == this.offset.keys && this.offset.all { (offs, ty) ->
                    ty.equivModuloPath(other.offset[offs]!!)
                }
            }

            override fun staticFieldOf(path: ObjectPath): LinearizedType {
                return this.copy(
                        path = this.path.staticFieldOf(path),
                        offset = this.offset.mapValues {
                            it.value.staticFieldOf(path)
                        }
                )
            }
        }

        data class Word(override val path: ObjectPath) : LinearizedType() {
            override val sizeInArray: BigInteger
                get() = EVM_WORD_SIZE
            override val isDynamic: Boolean
                get() = false

            override fun toSort(): DynamicSort? = null

            override fun equivModuloPath(other: LinearizedType): Boolean = other is Word

            override fun staticFieldOf(path: ObjectPath): LinearizedType {
                return this.copy(path = this.path.staticFieldOf(path))
            }
        }

        abstract fun toSort(): DynamicSort?
        abstract fun staticFieldOf(path: ObjectPath): LinearizedType
    }

    private companion object {
        private fun ObjectPath.staticFieldOf(parent: ObjectPath) : ObjectPath {
            return if(this is ObjectPathGen.Field && this.parent == parent) {
                ObjectPathGen.StaticArrayField(this.parent)
            } else if(this is WithParentPath<*>) {
                this.uncheckedAs<WithParentPath<ObjectPathAnalysis.ObjectRoot>>().let {
                    it.mapParent(it.parent.staticFieldOf(parent))
                }
            } else {
                throw IllegalArgumentException()
            }
        }

        /**
         *  find the smallest possible offset touched by this path (effectively, assume
         *  the loops in the path iterate zero times).
         *
         */
        private fun List<StrideStep>.toFirstElem(start: BigInteger) = this.fold(start) { Curr, x ->
            if(x !is StrideStep.ConstStep) {
                Curr
            } else {
                Curr + x.c
            }
        }

        fun findPaths(m: Map<BigInteger, TopLevelWrite>, targetOffset: BigInteger) : List<Unresolved> {
            return m.flatMap { (key, value) ->
                if(key >= targetOffset) {
                    listOf()
                } else if(value.const == null) {
                    listOf()
                } else if(targetOffset == value.const) {
                    listOf(Unresolved(root = key, fields = listOf()))
                } else if(targetOffset < value.const) {
                    listOf()
                } else {
                    val guessStart = targetOffset - value.const
                    if(guessStart > key) {
                        listOf()
                    } else {
                        findPaths(m, guessStart).map {
                            it + (key - guessStart)
                        }
                    }
                }
            }
        }
    }

    private fun getParentArray(toStep: EncodingState, q1: ElemPointer) : ValueQualifier.OffsetQualifier.DynamicStart? {
        return toStep.qualifiers[q1.parent]?.let {
            it as? ValueQualifier.OffsetQualifier.DynamicStart
        }?.takeIf {
            it.sort == DynamicSort.ARRAY
        }
    }

    /**
     * Abstract over the complication of structs vs arrays and how their child object offsets are computed. Given a pointer to a
     * dynamic object or array elem start, compute:
     * 1. The variable with the (unique) DynamicStart object
     * 2. The DynamicStart object itself, and
     * 3. The variable to which offsets must be added to yield child locations in the buffer.
     */
    private fun extractBase(k: TACSymbol.Var, toStep: EncodingState): DynamicObject? {
        val v = toStep.qualifiers[k]?.let { it as? ValueQualifier.OffsetQualifier } ?: return null
        return when(v) {
            is ValueQualifier.OffsetQualifier.DynamicStart -> if(v.sort == DynamicSort.ARRAY) {
                toStep.qualifiers.entries.singleOrNull { (_, v) ->
                    (v as? ValueQualifier.OffsetQualifier.ArrayElemStart)?.parent == k
                }?.let {(addBase, _) ->
                    DynamicObject(
                            dyn = v,
                            addBase = addBase,
                            dynVar = k
                    )
                }
            } else {
                DynamicObject(
                        dynVar = k,
                        addBase = k,
                        dyn = v
                )
            }
            is ValueQualifier.OffsetQualifier.ArrayElemStart -> toStep.qualifiers[v.parent]?.let {
                it as? ValueQualifier.OffsetQualifier.DynamicStart
            }?.let { d ->
                DynamicObject(
                        dyn = d,
                        dynVar = v.parent,
                        addBase = k
                )
            }
            else -> null
        }
    }

    override fun startBlock(encoderState: State, lva: Set<TACSymbol.Var>, referencedFromLive: Set<TACSymbol.Var>): State {
        val keepP = { it: TACSymbol.Var -> it in lva || it in referencedFromLive }
        return State(
                encoding = encoderState.encoding?.let {
                    it.copy(
                        qualifiers = it.qualifiers.retainAllKeys(keepP),
                        currPointer = it.currPointer?.takeIf(keepP),
                        nextPointer = it.nextPointer?.takeIf(keepP),
                        copyBuffers = it.copyBuffers.retainAllKeys(keepP)
                    )
                },
                finalizedState = encoderState.finalizedState.retainAllKeys(keepP)

        )
    }

    override fun collectReferenced(encoderState: State, referencedFromLive: MutableSet<TACSymbol.Var>, lva: Set<TACSymbol.Var>) {
        encoderState.finalizedState.forEach { (k, v) ->
            if(k !in lva) {
                return@forEach
            }
            v.buffer.values.flatMapTo(referencedFromLive) {
                it.objectPath.mapNotNull {
                    it.rootVar
                }
            }
        }
        if(encoderState.encoding != null) {
            encoderState.encoding.varRoots.flatMapTo(referencedFromLive) { (_, v) ->
                v.objectPath.mapNotNull { it.rootVar }
            }
            encoderState.encoding.qualifiers.entries.forEach { (k, v) ->
                if(k !in lva) {
                    return@forEach
                }
                v.collectReferenced(referencedFromLive)
            }
            encoderState.encoding.lastRootWrite?.let {
                referencedFromLive.add(it.symbol)
                referencedFromLive.addAll(it.baseVariables)
            }
            for((buff, operands) in encoderState.encoding.copyBuffers) {
                if(buff !in lva) {
                    continue
                }
                referencedFromLive.add(operands.srcOffset)
                (operands.srcLength as? TACSymbol.Var)?.let(referencedFromLive::add)
            }
        }
    }

    override fun endBlock(encoderState: State, last: LTACCmd, live: Set<TACSymbol.Var>): State {
        return encoderState
    }

    override fun finalizeBuffer(encoderState: State, conv: List<ConversionHints>, s: PointsToDomain, where: LTACCmd): State {
        if(encoderState.encoding == null) {
            return encoderState
        }
        val isPopForEncoder = conv.any {
            it is ConversionHints.Array && s.pointsToState.store[it.v]?.let {
                it as? WritablePointer
            } == encoderState.encoding.buffer
        }
        if(!isPopForEncoder) {
            return encoderState
        }
        val bufferResult = FinalizedBuffer(encoderState.encoding.varRoots)
        val finalized = conv.filterIsInstance<ConversionHints.Array>().map {
            it.v
        }
        if(encoderState.encoding.varRoots.isEmpty()) {
            logger.warn {
                "finalizing the allocation of $finalized but have no buffer contents? This is almost certainly wrong"
            }
            return encoderState.copy(
                encoding = null
            )
        }
        encodeCompletePoints[where.ptr] = IEncoderAnalysis.EncodeCompletePoint(
            buffer = encoderState.encoding.buffer,
            encoded = EncodeOutput.Alloc(finalized.toSet())
        )
        logger.info {
            "Finalized buffer: $finalized with $bufferResult @ $where"
        }
        return encoderState.copy(
                encoding = null,
                finalizedState = encoderState.finalizedState + finalized.associateWith { bufferResult }
        )
    }

    private val indexTracking = object : IndexTracking<ValueQualifier, StrideWithIndexing, Nothing>(
            numericDomain = numeric
    ) {
        override fun indexStepSizeFor(k: TACSymbol.Var, v: ValueQualifier, m: Map<TACSymbol.Var, ValueQualifier>, p: PointsToDomain): BigInteger? {
            return (v as? StrideWithIndexing)?.strideBy
        }

        override fun downcast(v: ValueQualifier): StrideWithIndexing? {
            return v as? StrideWithIndexing
        }
    }

    override fun interpolate(prev: PointsToDomain, next: PointsToDomain, summary: Map<TACSymbol.Var, TACExpr>): State {
        if(prev.encoderState.encoding == null || next.encoderState.encoding == null) {
            return next.encoderState
        }
        return next.encoderState.copy(
                encoding =  next.encoderState.encoding.copy(
                        qualifiers = indexTracking.interpolate(
                                prevM = prev.encoderState.encoding.qualifiers,
                                nextM = next.encoderState.encoding.qualifiers,
                                summary = summary,
                                next = next
                        ).first
                )
        )
    }

    override fun step(command: LTACCmd, s_: PointsToDomain) : State {
        return topLevelSemantics.step(command, s_)
    }

    override fun join(encoderState: State, thisContext: PointsToDomain, otherState: State, otherContext: PointsToDomain): State {
        return encoderState.join(this, otherState, thisContext, otherContext)
    }
}
