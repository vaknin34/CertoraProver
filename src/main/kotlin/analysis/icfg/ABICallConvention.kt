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

package analysis.icfg

import allocator.Allocator
import allocator.SuppressRemapWarning
import analysis.*
import analysis.pta.HeapType
import analysis.pta.IDecoderAnalysis
import analysis.pta.abi.*
import com.certora.collect.*
import datastructures.stdcollections.*
import evm.DEFAULT_SIGHASH_SIZE
import evm.EVM_WORD_SIZE
import instrumentation.calls.CalldataEncoding
import log.Logger
import log.LoggerTypes
import optimizer.UNINDEXED_PARTITION
import scene.ITACMethod
import tac.CallId
import tac.Tag
import utils.*
import vc.data.*
import vc.data.tacexprutil.ExprUnfolder
import java.math.BigInteger
import java.util.stream.Collectors
import kotlin.collections.filterValues
import kotlin.collections.listOf
import kotlin.collections.mutableMapOf
import kotlin.collections.mutableSetOf
import kotlin.collections.setOf
import kotlin.collections.setOfNotNull

private val logger = Logger(LoggerTypes.ABI)
/**
 * An intermediate result used during the code generation of [analysis.icfg.ABICallConvention.ObjectTraversal]
 * Each object traversal represents a "walk" of an object starting at the [analysis.icfg.ABICallConvention.ObjectTraversal]
 * [analysis.icfg.ABICallConvention.ObjectTraversal.VarRoot]. This traversal of some *concrete* object corresponds to a traversal
 * of the abstract object layout. As the abstract object layout (see [IndexedAbstractPointer]) determines how the logical
 * fields of an object are accessed (i.e., which memory partitions hold the fields for the object), each
 * "step" of the traversal requires the abstract object layout (wrapped up in an [IndexedAbstractPointer]) to know how to
 * generate each object field access.
 *
 * This is the role of the [TraversalIR]: it represents an intermediate step of the traversal; the first
 * component is the "concrete" part of the traversal: a sequence of commands that effects some (not necessarily strict)
 * prefix of the traversal. The latter component is the abstract component, it represents the abstract object layout
 * of the object reached by performing the _concrete_ traversal represented by the first component.
 */
private typealias TraversalIR = Pair<CommandWithRequiredDecls<TACCmd.Simple>, IndexedAbstractPointer>

/**
 * Collection of functionality to handle the interaction between callers and callees.
 *
 * The documentation of this class makes frequent reference to "abstract object layouts", see [IndexedAbstractPointer]
 * for a discussion of that term.
 */
object ABICallConvention {
    /**
     * Represents a traversal through some object in a memory space [traversal], and the memory layout [outputPointer] of the value
     * that is the *result* of that traversal. Thus, if [traversal] is [analysis.icfg.ABICallConvention.ObjectTraversal.VarRoot],
     * then [outputPointer] must equal the [traversal]'s [analysis.icfg.ABICallConvention.ObjectTraversal.VarRoot.abstractPointer].
     *
     * In other words, it is expected (but not check) that after traversing the [analysis.icfg.ABICallConvention.ObjectTraversal.VarRoot]'s
     * [analysis.icfg.ABICallConvention.ObjectTraversal.VarRoot.abstractPointer] with the abstract fields the correspond
     * to each step of the [analysis.icfg.ABICallConvention.ObjectTraversal] (e.g., [PartitionField.StructField] for
     * an [ObjectTraversal.StructField]) the result will be [outputPointer]. Indeed, this is the functionality exposed by
     * [mapWith] below.
     */
    data class PointerTraversal(
        val traversal: ObjectTraversal,
        val outputPointer: IndexedAbstractPointer
    ) {
        /**
         * Extend this [PointerTraversal] by following the abstract field [f] of [outputPointer],
         * and extending [traversal] via [cb]. It is expected (but not checked) that the extension of the [ObjectTraversal]
         * effected by [cb] "corresponds" to [f], e.g., if [f] [PartitionField.StructField] then [cb] extends [traversal]
         * with [ObjectTraversal.StructField].
         *
         * If the [outputPointer] does not have a model for [f] (i.e., [IndexedAbstractPointer.deref] returns null), or
         * [cb] returns null, this function returns null.
         */
        fun mapWith(f: PartitionField, cb: (ObjectTraversal) -> ObjectTraversal?) : PointerTraversal? {
            val (_, k) = outputPointer.deref(f) ?: return null
            return PointerTraversal(
                traversal = cb(traversal) ?: return null,
                outputPointer = k
            )
        }
    }

    /**
     * Represents a [PointerTraversal] with additional information about the abstract memory layout of where the
     * result should go. This is used in the context of decoding; [traversal] describes how to
     * traverse some argument, and [sourcePointer] indicates the abstract object layout of the result of that traversal.
     * [outputPointer] indicates the partitions which should be initialized to the "matching" partitions in [sourcePointer].
     *
     * We should refactor [IndexedAbstractPointer] to vary the type of partition information it gives out.
     */
    private data class BindingTraversal(
        val traversal: ObjectTraversal,
        val sourcePointer: IndexedAbstractPointer,
        val outputPointer: UnindexedTraversal
    )

    /**
     * Represents the core pieces of [ABIDecodeComplete] needed for matching; the type [decodedType], the buffer access
     * path being decoded from [decodedPath], and the abstract object layout in [decodedFields].
     */
    @SuppressRemapWarning
    data class DecodePath(
        val decodedType: HeapType,
        val decodedPath: DecoderAnalysis.BufferAccessPath,
        val decodedFields: Map<PartitionField, EncodedPartitions>?
    )

    /**
     * A representation of a path through an object starting at some variable root.
     * This is very similar to [ObjectPathGen], with a few exceptions:
     * 1. static array strides aren't allowed (maybe they should)
     * 2. array element information includes data necessary for code generation, particularly the index and the element size
     *
     * Folding the above information into [ObjectPathGen] and avoiding the apparently redundant class hierarchy was considered
     * and rejected, because tracking it in the other places used by the [ObjectPathGen] would be annoying, or impossible,
     * in which case the fields would all have to be made nullable. This is the lesser of two evils.
     */
    sealed class ObjectTraversal {
        protected fun TraversalIR.extendWithField(
            f: PartitionField,
            p: (PartitionLike<*>) -> CommandWithRequiredDecls<TACCmd.Simple>
        ): TraversalIR {
            val (part, nxt) = this.second.deref(f) ?: throw UnsupportedOperationException("Unexpected deref operation")
            val code = p(part)
            return this.first.merge(code) to nxt
        }

        /**
         * The start point of a traversal: a variable and the abstract object layout. *IMPORTANT*: When this class is created
         * it is assumed that [v] refers to a variable that is not in an inlined body, i.e., it's callIdx is 0.
         *
         * Further, if this object traversal is later used for code generation within an inlined body at call index C,
         * the variable [v] is assumed to exist with the call index C.
         *
         * In other words, if this code generation is performed at some call index, the variable [v] used in its construction
         * must still exist but with that call index now attached.
         */
        data class VarRoot(val v: TACSymbol.Var, val abstractPointer: IndexedAbstractPointer) : ObjectTraversal() {
            override fun codeGenInternal(output: TACSymbol.Var, callIdx: CallId): TraversalIR {
                val vAtCallIdx = v.at(callIdx).asSym()
                val rhs = if (v.tag == Tag.Bool && output.tag == Tag.Bit256) {
                    TACExpr.TernaryExp.Ite(vAtCallIdx, 0.asTACExpr, 1.asTACExpr)
                } else {
                    vAtCallIdx
                }
                return ExprUnfolder.unfoldPlusOneCmd("abiBool", rhs) {
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = output,
                        rhs = it,
                    )
                }.merge(output, v.at(callIdx)) to abstractPointer
            }
        }

        /**
         * Take the traversal represented by [parent] and traverse the struct field at [offset].
         */
        data class StructField(val offset: BigInteger, val parent: ObjectTraversal) : ObjectTraversal() {
            override fun codeGenInternal(output: TACSymbol.Var, callIdx: CallId): TraversalIR {
                val tmp = TACKeyword.TMP(Tag.Bit256, "!structbase").at(callIdx).toUnique("!")
                val ret = parent.codeGenInternal(tmp, callIdx)
                val offs = TACKeyword.TMP(Tag.Bit256, "!struct!$offset").at(callIdx).toUnique("!")
                return ret.extendWithField(PartitionField.StructField(offset)) { part ->
                    CommandWithRequiredDecls(
                        listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = offs,
                                rhs = TACExpr.Vec.Add(
                                    tmp.asSym(),
                                    offset.asTACSymbol().asSym()
                                )
                            )
                        ),
                        offs, tmp
                    ).merge(part.selectCommand(lhs = output, loc = offs))
                }
            }
        }

        /**
         * Take the traversal represented by [parent], and access the element at index [elem], where each element
         * has size [elemSize] (in practice, either one or [EVM_WORD_SIZE], aka 32)
         */
        data class ArrayElem(val elem: TACSymbol, val elemSize: BigInteger, val parent: ObjectTraversal) : ObjectTraversal() {
            override fun codeGenInternal(output: TACSymbol.Var, callIdx: CallId): TraversalIR {
                val tmp = TACKeyword.TMP(Tag.Bit256, "!arrayBase").at(callIdx).toUnique("!")
                val ret = parent.codeGenInternal(tmp, callIdx)
                val elemStart = TACKeyword.TMP(Tag.Bit256, "!dataStart").at(callIdx).toUnique("!")
                val elemOffs = TACKeyword.TMP(Tag.Bit256, "!elemOffs").at(callIdx).toUnique("!")
                val elemLoc = TACKeyword.TMP(Tag.Bit256, "!elemLoc").at(callIdx).toUnique("!")
                val elemAt = if(elem is TACSymbol.Var) {
                    elem.at(callIdx)
                } else {
                    elem
                }

                return ret.extendWithField(PartitionField.ArrayElement(elemSize.intValueExact())) { part ->
                    CommandWithRequiredDecls(
                        listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = elemStart,
                                rhs = TACExpr.Vec.Add(
                                    tmp.asSym(),
                                    EVM_WORD_SIZE.asTACSymbol().asSym() // compute start point
                                )
                            ),
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = elemOffs,
                                rhs = TACExpr.Vec.Mul(
                                    elemAt.asSym(),
                                    elemSize.asTACSymbol().asSym() // offset within the element segment
                                )
                            ),
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                lhs = elemLoc,
                                rhs = TACExpr.Vec.Add(
                                    elemStart.asSym(),
                                    elemOffs.asSym()
                                ) // position of the element
                            ),
                        ),
                        setOfNotNull(elemLoc, elemOffs, elemStart, tmp,
                            elemAt as? TACSymbol.Var)
                    ).merge(part.selectCommand(lhs = output, loc = elemLoc))
                }
            }
        }

        /**
         * A read of an array at the point represented by [parent].
         */
        data class ArrayLength(private val parent: ObjectTraversal) : ObjectTraversal() {
            override fun codeGenInternal(output: TACSymbol.Var, callIdx: CallId): TraversalIR {
                val tmp = TACKeyword.TMP(Tag.Bit256, "!array").toUnique("!").at(callIdx)
                return parent.codeGenInternal(tmp, callIdx).extendWithField(PartitionField.ArrayLength) { part ->
                    part.selectCommand(lhs = output, loc = tmp)
                }
            }

        }

        /**
         * Generate code that performs the object traversal (which bottoms out at some variable [VarRoot]),
         * placing the result of the traversal into [output]. Intermediate code should be generated
         * using call index [callIdx]
         */
        fun codeGen(output: TACSymbol.Var, callIdx: CallId) : CommandWithRequiredDecls<TACCmd.Simple> {
            return codeGenInternal(output, callIdx).first
        }

        /**
         * Generate code that places the value conceptually represented by `this` into the variable [output].
         * The code generation is done in inlining context [callIdx]: variables referenced in this and temp variables
         * should have their [TACSymbol.Var.callIndex] fields set appropriately.
         *
         * As the name suggests, this is the "internal" variant, used for intermediate steps, and thus returns
         * a [TraversalIR] which is needed by "future" steps (see [TraversalIR] for details).
         */
        abstract fun codeGenInternal(output: TACSymbol.Var, callIdx: CallId) : TraversalIR
    }

    /**
     * Represents a single argument when an external call directly passes a value in its calldata into the buffer
     * of another external call (i.e., it represents an argument to an external function coming directly from calldata)
     */
    data class CalldataArg(
        val root: ObjectPathAnalysis.ObjectRoot.CalldataRoot,
        val type: HeapType
    )

    /**
     * Represents all uses of (ABI encoded) calldata within a method's body. If this class is produced for a method
     * then *every* calldata access is *provably* part of one of the accesses below, and if those accesses can be
     * rewritten in terms of high-level operations then *all* calldata encoding can be removed.
     */
    data class ABIExpected(
        /**
         * `callSiteReads.get(k).get(ind) = arg` means that at callsite with ID k, argument ind is coming directly from the
         * calldata buffer as represented by the associated [CalldataArg]
         */
        val callSiteReads: Map<Int, Map<BigInteger, CalldataArg>>,
        /**
         * `decodes.get(k) = dec` means that the decode represented by the [ABIDecodeComplete] annotation with id
         * `k` is decoding [DecodePath.decodedPath] from calldata, and expecting to get a value of type [DecodePath.decodedType].
         * The (unindexed) abstract object layout of the decoded object are given by [DecodePath.decodedFields].
         */
        val decodes: Map<Int, DecodePath>,
        /**
         * Every access at the indices in represented in [primitive] are expected to be ints.
         *
         * Q) Couldn't these be represented in decodes?
         * A) in principle yes, but we don't associate each primitve access of calldata with an annotation that has an id.
         *   Unlike primitive reads, decodes are "more complicated" and need a lot more information for the purposes
         *   of instrumentation.
         */
        val primitive : Set<BigInteger>,
        /**
         * `directRead.get(k) = callRead` means that the [ABIDirectRead] with id k is reading the value at location
         * represented by [IDecoderAnalysis.DirectCalldataRead]
         *
         * Q) So, why aren't primitives represented here?
         * A) This is a closer fit except, again, we don't actually tag any primitive calldata reads. Further, the reads
         * in primitive are known to be exactly at a constant offset and are "self contained". In contrast, the reads
         * of [IDecoderAnalysis.DirectCalldataRead] can potentially traverse arbitrary structures in the calldata, and
         * thus require code gen for the purposes of modeling the access and require cleaning up validation and decoding
         * "boilerplate". In contract the accesses in [primitive] "just happen", they are a direct read of a constnat offset,
         * which is checked to match up directly with a scalar value in the caller.
         */
        val directReads: Map<Int, IDecoderAnalysis.DirectCalldataRead>
    )

    /**
     * Represents the value passed to an external call.
     */
    sealed class PassedArgument

    /**
     * A literal constant with value [const]
     */
    data class Constant(val const: BigInteger) : PassedArgument()

    /**
     * An argument that comes comes from the caller's calldata; [path] represents a traversal of an object,
     * the root of which are the synthetic "abi argument" names generated by the caller matching process see [callerMatchesCallee]
     */
    data class ResolvedPath(val path: ObjectTraversal) : PassedArgument()

    /**
     * An argument from the caller's own memory space, held in the variable [sym]
     */
    data class ResolvedSymbol(val sym: TACSymbol.Var) : PassedArgument()

    /**
     * Common class for a resolution, i.e., a match between the caller and callee, describing how uses calldata in the
     * callee should be expressed in object traversals over the synthetic abiArg variables that represent the top-level
     * arguments passed to this callee.
     */
    sealed class ABIResolution {
        /**
         * Each key in the map corresponds to the id of a [ABIDecodeComplete] annotation, the corresponding value
         * describes how to access the value being decoded, expressed as a traversal over the synthetic arguments
         * passed to this function.
         *
         * NB the use of [ObjectTraversal] here (and in [directReads] below) instead of [PointerTraversal] (as in [ABIExpected]);
         * that is, here we do not include information about the abstract object layout of the decoded
         * object. It turns out that information about the layout is necessary for computing the initialization terms,
         * which is handled with [initialization]. When actually instrumenting the decode however, only the traversal
         * is required.
         */
        abstract val decode: Map<Int, ObjectTraversal>

        /**
         * Each key in the map corresponds to the id of a [ABIDirectRead] annotation, the corresponding value
         * describes how to access the (primitive) value being read, expressed as a traversal over the synthetic
         * arguments passed to this function.
         */
        abstract val directReads: Map<Int, ObjectTraversal>

        /**
         * The scalarized calldata index (i.e., each offset in [ABIExpected.primitive]) is expected to be
         * placed in the synthetic variable in the codomain.
         */
        abstract val primitiveBinding: Map<BigInteger, TACSymbol.Var>

        /**
         * Describes how the partitions in the callee should be initialized
         */
        abstract val initialization: Map<UnindexedPartition, PartitionLike<*>>
    }

    /**
     * Describes how this function uses calldata in terms of the synthetic arguments. Unlike [ABIFullBinding] there
     * is no information (yet) about what values to bind to the synthetic abiArg variables, only what to do with those
     * variables once the binding is fully resolved.
     */
    @SuppressRemapWarning
    data class ABICalleeBinding(
        override val decode: Map<Int, ObjectTraversal>,
        /**
         * `callSiteUse.get(k).get(ind) = obj` means that the callsite with id `k`, the argument `ind` needs to be bound to
         * the value stored in calldata, as expressed in `obj`. Note that other arguments at `k` that are not coming
         * directly from calldata do not need special ABI handling to be resolved.
         */
        val callSiteUse: Map<Int, Map<BigInteger, PointerTraversal>>,
        /**
         * Maps the arguments position to the synthetic name. E.g. `0 => abiArg!1` `32 => abiArg!27` etc.
         * When this binding information is fully resolved, this information is used to generate the binding of [PassedArgument]
         * to the target variable.
         */
        val argNames: Map<BigInteger, TACSymbol.Var>,
        override val directReads: Map<Int, ObjectTraversal>,
        override val primitiveBinding: Map<BigInteger, TACSymbol.Var>,
        override val initialization: Map<UnindexedPartition, PartitionLike<*>>
    ) : ABIResolution()

    /**
     * Represents a fully resolved "binding" between a callee and caller, in addition to describing how the synthetic arguments
     * within the callee's body are used, the [argToFormalBind] field describes how those synthetic arguments are bound
     * (for some particular call site)
     */
    @SuppressRemapWarning
    data class ABIFullBinding(
        override val decode: Map<Int, ObjectTraversal>,
        /**
         * A list of `(passedArg, v)` where each `v` is expected to be a synthetic abiArg name, and the corresponding
         * `passedArg` is the value (expressed as a [PassedArgument]) that should be bound to that name in the callee.
         */
        val argToFormalBind : List<Pair<PassedArgument, TACSymbol.Var>>,
        override val directReads: Map<Int, ObjectTraversal>,
        override val primitiveBinding: Map<BigInteger, TACSymbol.Var>,
        override val initialization: Map<UnindexedPartition, PartitionLike<*>>
    ) : ABIResolution()

    /**
     * If all uses of calldata within [method] can be completely classified into known usage pattern (via [ABIEncodeComplete],
     * [ABIDecodeComplete], etc.) then return an object that describes all of the "high-level" operations on calldata
     * that occur in this method. A return value of null indicates that some use of calldata could not be associated
     * with some knowable high-level operation, and thus it is not safe to ellide direct encoding of the calldata buffer)
     */
    fun extractExpected(
        method: ITACMethod
    ) : ABIExpected? {
        val core = method.code as CoreTACProgram
        val loop = getNaturalLoops(core.analysisCache.graph)
        fun withinLoop(p: CmdPointer) = loop.any {
            p.block in it.body
        }

        /**
         * Find all decode annotations, and mark those that are within a loop of some sort.
         */
        val decodePlusLoop = core.parallelLtacStream().mapNotNull {
            it.ptr `to?` it.maybeAnnotation(ABIDecodeComplete.META_KEY)?.takeIf { abi -> abi.sourceBuffer.meta.containsKey(TACMeta.IS_CALLDATA) }
        }.collect(Collectors.toMap({ it.second.id }) { (ptr, decode) ->
            withinLoop(ptr) to DecodePath(
                decodedType = decode.decodedType,
                decodedPath = decode.sourcePath,
                decodedFields = decode.fieldRelations
            )
        })

        /**
         * The round-tripping of data through an ABI buffer will remove all aliasing. That is, if you pass: `[a, a]`
         * (where `a` is an array of some type) through an ABI buffer to some callee who binds it to argument `x`,
         * `x[0]` and `x[1]` will **not** alias in the callee (but will have identical values). Further, decoding the same
         * argument multiple times should yield distinct object.
         *
         * The change to direct passing *changes* this behavior, aliases in the caller will be reflected
         * in the callee. Similarly, multiple decodes of the same calldata location (moving a `calldata` argument
         * into `memory) will just return the same pointer. However, this is only a problem if the callee writes into a location
         * that is aliased. Then, and only then, aliasing (or lack thereof) matter.
         *
         * Determining whether there is aliasing among decoded objects or among fields of a single arguments is hard and annoying (and
         * undecidable anyway). We instead over-approximate. We find all partitions that are reachable from some decode,
         * and then filter by those partitions which are "reachable" along multiple paths. If a partition is reachable
         * via multiple paths, then there is potentially sharing; i.e., the partition holds data with different logical identities.
         *
         * We actually approximate "multiple" paths by reference counting; i.e., counting how many times we see a partition
         * in the [ABIDecodeComplete.fieldRelations] structure. However, any partitions reachable through an array element
         * or from a decode which appears within a loop is (artifically) counted twice.
         *
         * At the end of this process, we take those partitions with a "reference" counter greater than 1 as being reachable
         * from multiple paths. We then scan to see if these partitions are read only (outside any decoding code). If they
         * are, then we can make this change to aliasing behavior: the client code won't "notice". If, however, they are not
         * read only, we conservatively bail out.
         */
        val mustNotWritePartitions = decodePlusLoop.asSequence().flatMap { (_, v) ->
            val (inLoop, dec) = v
            if(dec.decodedFields == null) {
                return@flatMap emptySequence<Pair<UnindexedPartition, Int>>()
            }
            val refCount = if(inLoop) { 2 } else { 1 }
            suspend fun SequenceScope<Pair<UnindexedPartition, Int>>.recurse(e: Map<PartitionField, EncodedPartitions>, refCount: Int) {
                for((f, p) in e) {
                    yield(p.part to refCount)
                    if(p is EncodedPartitions.ReferenceValue) {
                        recurse(p.fields, if(f is PartitionField.ArrayElement) {
                            2
                        } else { refCount })
                    }
                }
            }
            sequence {
                recurse(dec.decodedFields, refCount)
            }
        }.groupBy({ it.first }, { it.second }).mapValues { (_, refCount) ->
            refCount.takeIf(Collection<Int>::isNotEmpty)?.sum() ?: 0
        }.keysMatching { _, count ->
            count > 1
        }
        if(mustNotWritePartitions.isNotEmpty()) {
            val writesPotentiallyAliasingDecodes = core.parallelLtacStream().anyMatch {
                if(ABIAnnotator.CODE_FOR in it.cmd.meta) {
                    return@anyMatch false
                }
                val writtenPart = when(it.cmd) {
                    is TACCmd.Simple.ByteLongCopy -> {
                        it.cmd.dstBase.meta.find(UNINDEXED_PARTITION)
                    }
                    is TACCmd.Simple.AssigningCmd.ByteStore -> {
                        it.cmd.base.meta.find(UNINDEXED_PARTITION)
                    }
                    is TACCmd.Simple.AssigningCmd.ByteStoreSingle -> {
                        it.cmd.meta.find(UNINDEXED_PARTITION)
                    }
                    is TACCmd.Simple.SummaryCmd -> {
                        if(it.cmd.summ !is ICallCoreSummary) {
                            return@anyMatch false
                        }
                        (it.cmd.summ.outBase as? TACSymbol.Var)?.meta?.find(UNINDEXED_PARTITION)
                    }
                    else -> return@anyMatch false
                }
                writtenPart in mustNotWritePartitions
            }
            if(writesPotentiallyAliasingDecodes) {
                logger.warn {
                    "Found writes to potential aliases in the decoded body for ${core.name}, returning null"
                }
                return null
            }
        }

        val decode = decodePlusLoop.mapValues { it.value.second }

        /**
         * In some cases we read from calldata, but do so intentionally reading past the end of the array to fill
         * an array with zeroes. Find these patterns and mark them as fine (in which case the default initialization
         * of calldata _should_ be sufficient)
         *
         * FIXME(jtoman): make sure that the above is actually true???
         */
        val gvn = core.analysisCache.gvn // ensure this lazy val is initialized before its used in a parallel stream
        val calldataInits = core.parallelLtacStream().filter {
            it.cmd is TACCmd.Simple.ByteLongCopy && it.cmd.srcBase == TACKeyword.CALLDATA.toVar() && it.cmd.srcOffset is TACSymbol.Var &&
                    TACKeyword.CALLDATASIZE.toVar() in gvn.equivBefore(it.ptr, it.cmd.srcOffset)
        }.map {
            it.ptr
        }.collect(Collectors.toSet())

        /**
         * If there is a calldata encoding into a buffer that it is not "used" by an external call, then we can't remove calldata
         * encoding, so return null here.
         *
         * TODO CERT-5935
         *  it's possible for us to not remove encoding while still doing direct passing for decodes. This is too strict
         */
        val calldataEncodesToScratch = core.parallelLtacStream().mapNotNull {
            it.maybeAnnotation(ABIEncodeComplete.META_KEY)?.takeIf {
                it.target is EncodeOutput.Scratch && it.buffer.buffer.any { (_, tlv) ->
                    tlv is TopLevelValue.Path && tlv.paths.any {
                        it.root is ObjectPathAnalysis.ObjectRoot.CalldataRoot
                    }
                }
            }
        }.map { it.id }
            .collect(Collectors.toSet())

        val callSiteEncodes = core.parallelLtacStream().mapNotNull {
            it.snarrowOrNull<CallSummary>()?.callConvention?.input?.encodedArguments
        }.map { it.encodeId }
            .collect(Collectors.toSet())

        if(!callSiteEncodes.containsAll(calldataEncodesToScratch)) {
            logger.warn {
                "Not all encodes are matched in ${core.name}, to a call-site use: ${calldataEncodesToScratch - callSiteEncodes}"
            }
            return null
        }

        /**
         * Find all commands that use calldata that are not classified as part of a high-level calldata operation (as indicated
         * by the presence of [ABIAnnotator.CODE_FOR] meta or which have not explicitly identified
         * as being part of the initialization pattern
         */
        val reads = core.parallelLtacStream().filter {
            ABIAnnotator.CODE_FOR !in it.cmd.meta  && it.ptr !in calldataInits
        }.filter {
            it.cmd.getFreeVarsOfRhs().any {
                it.meta.containsKey(TACMeta.IS_CALLDATA) || it == TACKeyword.CALLDATA.toVar()
            }
        }.collect(Collectors.toSet())
        val primitiveReads = mutableSetOf<BigInteger>()
        for(r in reads) {
            /**
             * The ABI decode annotations "reference" calldata, but aren't interesting for our purposes
             */
            if(r.cmd is TACCmd.Simple.AnnotationCmd) {
                continue
            }
            /**
             * If this isn't a read of a scalarized calldata location (as indicated by the three checks below)
             * we return null, the code is using calldata is some unexpected, unclassifiable way
             */
            if(r.cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
                logger.debug { "${core.name}: ${r.cmd} not assignExpCmd"}
                return null
            }
            if(r.cmd.rhs !is TACExpr.Sym.Var) {
                logger.debug { "${core.name}: ${r.cmd} rhs not var"}
                return null
            }
            val idx = r.cmd.rhs.s.meta.find(TACMeta.CALLDATA_OFFSET)?.minus(DEFAULT_SIGHASH_SIZE) ?: run {
                logger.debug { "${core.name}: ${r.cmd.rhs} did not find calldata_offset meta"}
                return null
            }
            primitiveReads.add(idx)
        }
        /**
         * Now that we now all calldata uses are full classified, let's package those uses up into the friendly
         * [ABIExpected] representation
         */
        val callArg = core.parallelLtacStream().mapNotNull {
            it.snarrowOrNull<CallSummary>()
        }.mapNotNull { s ->
            val id = s.summaryId
            /**
             * Find, for each callsite, the argument indices that are directly passing through a calldata object
             * (and the expected type, as determined by the encoder analysis)
             */
            id `to?` s.callConvention.input.encodedArguments?.encodedArgs?.let { enc ->
                enc.filterValues {
                    it is ABIValue.Symbol && it.sym is ObjectPathAnalysis.ObjectRoot.CalldataRoot
                }.entries.associate { (ind, ab) ->
                    ind to CalldataArg(
                        (ab as ABIValue.Symbol).sym as ObjectPathAnalysis.ObjectRoot.CalldataRoot,
                        ab.type
                    )
                }
            }
        }.collect(Collectors.toMap({it.first}, {it.second}))

        /**
         * Find usages of calldata scalars in re-encode to other callee, and add them to the primitiveRead map,
         * ensuring we bind them at inlining time.
         */
        fun effectivelyPrimitive(arg: CalldataArg): Boolean {
            if (arg.root.fieldDepth != 0
                || arg.root.bp !is DecoderAnalysis.BufferAccessPath.Offset
                || arg.root.bp.base !is DecoderAnalysis.BufferAccessPath.Root) {
                return false
            }

            return when(val t = arg.type) {
                is HeapType.OffsetMap ->
                        !t.isDynamic() && t.fieldTypes[BigInteger.ZERO] is HeapType.Int

                is HeapType.Int ->
                    true

                else ->
                    false
            }
        }
        callArg.forEachEntry { (_, ent) ->
            ent.forEachEntry inner@{ (_, sym) ->
                if (!effectivelyPrimitive(sym)) {
                    return@inner
                }
                val offs = (sym.root.bp as DecoderAnalysis.BufferAccessPath.Offset).offset
                if((method.calldataEncoding as CalldataEncoding).byteOffsetToScalar.any { (r, _) ->
                        r.from == (offs + DEFAULT_SIGHASH_SIZE) && (r.to - r.from + BigInteger.ONE) == EVM_WORD_SIZE
                }) {
                    primitiveReads.add(offs)
                }
            }
        }


        /**
         * and finally, get all direct reads (i.e., `foo.bar.myArray[i]` where foo is marked
         * has having calldata storage)
         */
        val directReads = core.parallelLtacStream().mapNotNull { it.maybeAnnotation(ABIDirectRead.META_KEY) }
            .collect(Collectors.toMap({ it.id }, { it.path }))

        return ABIExpected(
            callSiteReads = callArg,
            decodes = decode,
            primitive = primitiveReads,
            directReads = directReads
        ).also {
            logger.trace {
                "extractExpected ${core.name} $it"
            }
        }
    }

    /**
     * Helper class used to consistent generate names for each logical argument that have been encoded
     * into the calldata buffer. These names are generated on demand during the matching process.
     */
    private class ArgNodeManager {
        private val args = mutableMapOf<BigInteger, TACSymbol.Var>()
        fun variableForRoot(v: BigInteger) = args.computeIfAbsent(v) {
            val id = Allocator.getFreshId(Allocator.Id.SPLIT_ARG)
            TACSymbol.Var("abiArg!$id", Tag.Bit256)
        }

        fun toArgNames() : Map<BigInteger, TACSymbol.Var> = args
    }

    /**
     * Instructions (a recipe if you like) about how to transform a buffer access path into an [ObjectTraversal]. As discussed
     * in many other places, the [analysis.pta.abi.DecoderAnalysis.BufferAccessPath] class is not appropriate for the purposes
     * of describing the logical location of a value within a buffer, only its physical location. For example, depending
     * on the enclosing types, the same buffer access path can correspond to: a field within a struct, a "top level" location,
     * a field within a struct within a static array, etc. etc.
     *
     * The only way to disambiguate the logical location represented by a [analysis.pta.abi.DecoderAnalysis.BufferAccessPath]
     * is with type information: each type (and all "value locations" within that type) can be unambiguously assigned
     * a buffer access path (but again, the reverse is *not* true). Thus, the [ObjectTraversalConstructor] records the
     * correspondence between a [analysis.pta.abi.DecoderAnalysis.BufferAccessPath] and the logical location it represents.
     * It is expected this [ObjectTraversalConstructor] is built up incrementally during the traversal of a type
     * known to exist at the roots of a calldata buffer. As a benefit, this class also extracts the index symbols
     * being used in accessing within an array, transferring that information to the [ObjectTraversal]
     */
    private sealed class ObjectTraversalConstructor {
        /**
         * Give the [analysis.pta.abi.DecoderAnalysis.BufferAccessPath] that is represented by this [ObjectTraversalConstructor]
         */
        abstract fun toBufferPath(): DecoderAnalysis.BufferAccessPath

        /**
         * Given a [buffer] that is (expected) to satisfy `this.toBufferPath().nonIndexed() == buffer.nonIndexed()`,
         * and an oracle for generating consistent abi argument names, return the [ObjectTraversal] that describes
         * how to access the same location of [buffer] but in terms of direct field/element accesses on the (synthetic)
         * abi argument names generated by [argRoots]
         */
        abstract fun consumeToObjectPath(buffer: DecoderAnalysis.BufferAccessPath, argRoots: ArgNodeManager) : PointerTraversal?

        data class ArrayElem(val parent: ObjectTraversalConstructor, val eSz: BigInteger) : ObjectTraversalConstructor() {
            override fun toBufferPath(): DecoderAnalysis.BufferAccessPath {
                return DecoderAnalysis.BufferAccessPath.ArrayElemOf(parent = parent.toBufferPath(), indices = setOf())
            }

            override fun consumeToObjectPath(
                buffer: DecoderAnalysis.BufferAccessPath,
                argRoots: ArgNodeManager
            ): PointerTraversal? {
                return parent.consumeToObjectPath((buffer as DecoderAnalysis.BufferAccessPath.ArrayElemOf).parent, argRoots)?.mapWith(PartitionField.ArrayElement(eSz.intValueExact())) {
                    ObjectTraversal.ArrayElem(
                        parent = it,
                        elem = buffer.indices.firstOrNull() ?: return@mapWith null,
                        elemSize = eSz
                    )
                }
            }
        }

        data class ArrayLength(val parent: ObjectTraversalConstructor) : ObjectTraversalConstructor() {
            override fun toBufferPath(): DecoderAnalysis.BufferAccessPath {
                return DecoderAnalysis.BufferAccessPath.Offset(BigInteger.ZERO, parent.toBufferPath())
            }

            override fun consumeToObjectPath(
                buffer: DecoderAnalysis.BufferAccessPath,
                argRoots: ArgNodeManager
            ): PointerTraversal? {
                val arrayParent = (buffer as DecoderAnalysis.BufferAccessPath.Offset).base as DecoderAnalysis.BufferAccessPath.Deref
                return parent.consumeToObjectPath(arrayParent, argRoots)?.mapWith(PartitionField.ArrayLength) {
                    ObjectTraversal.ArrayLength(
                        it
                    )
                }
            }
        }

        /**
         * As noted elesewhere, a single offset within a calldata buffer can correspond to multiple "logical" fields.
         * Thus, [offset] is the physical offset within a buffer, and [fields] are the logical fields that are traversed to
         * reach that offset. It is expected that `sum(fields) == offset` (and this is a representation invariant
         * checked at object construction time)
         */
        data class Offset(val parent: ObjectTraversalConstructor, val offset: BigInteger, val fields: List<BigInteger>) : ObjectTraversalConstructor() {
            init {
                check(offset == fields.fold(BigInteger.ZERO, BigInteger::add))
            }
            override fun toBufferPath(): DecoderAnalysis.BufferAccessPath {
                return DecoderAnalysis.BufferAccessPath.Offset(
                    offset = offset,
                    base = parent.toBufferPath()
                )
            }

            override fun consumeToObjectPath(
                buffer: DecoderAnalysis.BufferAccessPath,
                argRoots: ArgNodeManager
            ): PointerTraversal? {
                return parent.consumeToObjectPath(
                    (buffer as DecoderAnalysis.BufferAccessPath.Offset).base,
                    argRoots
                )?.let {
                    fields.monadicFold(it) { acc: PointerTraversal, fld: BigInteger ->
                        acc.mapWith(PartitionField.StructField(fld)) { parent ->
                            ObjectTraversal.StructField(
                                offset = fld,
                                parent = parent
                            )
                        }
                    }
                }
            }
        }

        /**
         * Unlike the other elements, the Deref field doesn't actually correspond to anything at the object
         * level
         */
        data class Deref(val parent: ObjectTraversalConstructor) : ObjectTraversalConstructor() {
            override fun toBufferPath(): DecoderAnalysis.BufferAccessPath {
                return DecoderAnalysis.BufferAccessPath.Deref(
                    parent = this.parent.toBufferPath()
                )
            }

            override fun consumeToObjectPath(
                buffer: DecoderAnalysis.BufferAccessPath,
                argRoots: ArgNodeManager
            ): PointerTraversal? {
                return parent.consumeToObjectPath((buffer as DecoderAnalysis.BufferAccessPath.Deref).parent, argRoots)
            }
        }

        data class Root(val root: BigInteger, val abstractPointer: IndexedAbstractPointer) : ObjectTraversalConstructor() {
            override fun toBufferPath(): DecoderAnalysis.BufferAccessPath {
                return DecoderAnalysis.BufferAccessPath.Offset(
                    offset = root,
                    base = DecoderAnalysis.BufferAccessPath.Root
                )
            }

            override fun consumeToObjectPath(
                buffer: DecoderAnalysis.BufferAccessPath,
                argRoots: ArgNodeManager
            ): PointerTraversal {
                return PointerTraversal(argRoots.variableForRoot(root).let {
                    ObjectTraversal.VarRoot(
                        it,
                        abstractPointer
                    )
                }, abstractPointer)
            }
        }
    }

    /**
     * Given a caller that is sending an ABI encoded buffer described by [enc_]
     * to a function that is expecting a calldata buffer with [expected]: check if the "shape" of the encoding
     * in [enc_] matches the expected layout expressed in [expected], and generate a high-level description of
     * how to express the low-level operations recorded in [expected] as high-level accesses (in the form of [ObjectTraversal]
     * objects) over synthetic "abiArg" names that should later be bound to hold the logical arguments encoded in [enc_].
     */
    fun callerMatchesCallee(
        enc_: ABIArgumentEncoding,
        expected: ABIExpected,
        callerMemorySpace: AbstractMemorySpace,
        callerABIResolution: Map<BigInteger, PointerTraversal>?
    ) : Either<ABICalleeBinding, () -> String> {
        val enc = enc_.encodedArgs
        val arg = ArgNodeManager()

        logger.trace {
            "callerMatchesCallee enc: $enc_ expected: $expected "
        }

        fun err(m: () -> String): Either<Nothing, () -> String> {
            logger.debug {
                "callerMatchesCallee: ${enc_.encodeId} ${m()}"
            }
            return m.toRight()
        }

        /**
         * This is the easy check first: if the locations we expected to be direct, constant offset integer values
         * are not according to the caller, immediately fail and return null.
         */
        if (!expected.primitive.all { enc[it]?.type == HeapType.Int }) {
            return err {
                "Did not match primitive layout: ${expected.primitive.filter { enc[it]?.type != HeapType.Int }}"
            }
        }
        /**
         * As mentioned in the documentation for [ObjectTraversalConstructor], the expected way to figure out what
         * buffer access paths are expected to correspond to which logical name is to traverse a type that starts
         * at some constant offset in the calldata buffer. At each point along this traversal, (implemented in
         * [typesAtPath]) we record the buffer access path at that point, the type of value that "starts" at that physical
         * location, and the corresponding [ObjectTraversalConstructor], which describes how to turn that physical
         * location (i.e., [analysis.pta.abi.DecoderAnalysis.BufferAccessPath] into an [ObjectTraversal])
         *
         * Note that it is impossible to have multiple instances of the same type at the same buffer access path
         * that have different logical identities, assuming a coherently laid out calldata.
         */
        val paths = mutableMapOf<DecoderAnalysis.BufferAccessPath, MutableMap<HeapType, ObjectTraversalConstructor>>()
        for((offs, aV) in enc.entries) {
            val root = ObjectTraversalConstructor.Root(
                root = offs,
                abstractPointer = if (aV.type is HeapType.ReferenceType) {
                    callerABIResolution?.get(offs)?.outputPointer ?: when (aV) {
                        is ABIValue.Constant -> return err {
                            "Have constant argument $aV passed as reference type for argument $offs"
                        }
                        is ABIValue.Symbol -> {
                            /**
                             * What about calldata roots? Well, in that case, we would have expected
                             * the [callerABIResolution] lookup above to succeed, hence why we fail if this
                             * is a non-symbol argument
                             */
                            if (aV.sym !is ObjectPathAnalysis.ObjectRoot.V) {
                                return err {
                                    "Have non-variable root ${aV.sym} for argument at $offs"
                                }
                            }
                            callerMemorySpace.pointerFor(aV.partitionRelation ?: return err {
                                "No partition relationship for a reference type argument $aV at $offs"
                            })
                        }
                    }
                } else {
                    IndexedAbstractPointer.nullaryPointer()
                }
            )
            val contentPath = if(aV.type.isDynamic()) {
                ObjectTraversalConstructor.Deref(root)
            } else {
                root
            }
            /*
             * type at path is expected to be called with the location of the "contents" of the value with the
             * given type, hence the addition of Deref above before this call
             */
            if(!typesAtPath(
                contentPath, ty = aV.type, output = paths
            )) {
                /*
                  If typesAtPath returns false, then something has gone wrong in traversing the types and the calldata
                  buffer is, somehow, not coherent. Conservatively bail out.
                 */
                return err {
                    "typesAtPath(${contentPath}, ${aV.type}, ${paths}) = false"
                }
            }
        }
        val decodeBinding = mutableMapOf<Int, BindingTraversal>()

        for((id, dec) in expected.decodes) {
            val (ty, bap, part) = dec
            val pathGen = paths[bap.nonIndexed()]?.get(ty) ?: return err {
                "paths[${bap.nonIndexed()}].get($ty) path_lookup=${paths[bap.nonIndexed()]}"
            }
            decodeBinding[id] = pathGen.consumeToObjectPath(bap, arg)?.let {
                BindingTraversal(
                    traversal = it.traversal,
                    sourcePointer = it.outputPointer,
                    outputPointer = UnindexedTraversal(part ?: return err {
                        "no partitions for decode $id type = $ty, path = $bap"
                    })
                )
            } ?: return err {
                "pathGen.consumeToObjectPath(${bap}, ${arg}) == null"
            }
        }

        val initializationMap = when(val initTerm = computeInitializationMap(decodeBinding)) {
            is Either.Left -> initTerm.d
            is Either.Right -> return err(initTerm.d)
        }

        /**
         * Callsite usage is a *little* bit more complicated, thanks to the decode analysis and encode analysis
         * using somewhat inconsistent buffer access paths to refer to the same logical value
         */
        val callSiteBinding = mutableMapOf<Int, MutableMap<BigInteger, PointerTraversal>>()
        for((id, callRoots) in expected.callSiteReads) {
            for((argInd, cdataArg) in callRoots) {
                val possibleTypes = paths[cdataArg.root.bp.nonIndexed()]
                    ?: return err {
                        "did not find path for ${cdataArg.root.bp.nonIndexed()}"
                    }
                /*
                  If a static struct (as per the ABI specification) with its own struct fields
                  occurs in the calldata buffer, then a single buffer access can correspond to multiple
                  possible struct types (each with their own ObjectPathTraversal).

                  Luckily we can disambiguate using the inline offsets (which encode the logical fields
                  of a static struct that are traversed as part of argument passing). So we start with all possible
                  struct types at the "start" buffer access path (the cdataArg.root.bp), and follow the struct fields
                  encoded in the inlineOffsets. At the end of this process we expect to be left with a single remaining
                  value, which matches the expected type of the argument we are passing.
                 */
                var depth = 0
                var acc = possibleTypes.entries.map { (type, traversal) ->
                    type to { ->
                        traversal.consumeToObjectPath(cdataArg.root.bp, arg)
                    }
                }
                while(depth < cdataArg.root.fieldDepth) {
                    acc = acc.mapNotNull { (ty, cons) ->
                        if(ty !is HeapType.OffsetMap) {
                            return@mapNotNull null
                        } else {
                            ty.fieldTypes[BigInteger.ZERO]?.to { ->
                                cons()?.let { p ->
                                    p.mapWith(PartitionField.StructField(BigInteger.ZERO)) {
                                        ObjectTraversal.StructField(
                                            offset = BigInteger.ZERO, parent = it
                                        )
                                    }
                                }
                            }
                        }
                    }
                   depth++
                }
                val passedObject = acc.singleOrNull {
                    it.first == cdataArg.type
                }?.second?.invoke() ?: return err {
                    "Pass through object matching failed, callee call-site id = $id, arg = $argInd type = ${cdataArg.type}, passthrough path = ${cdataArg.root}"
                }
                /*
                  We have determined thhat, at the callsite with id, the argInd^th argument is an object coming
                  directly from calldata, as described by the passedObject ObjectTraversal
                 */
                callSiteBinding.computeIfAbsent(id) {
                    mutableMapOf()
                }.put(argInd, passedObject)
            }
        }
        val directReads = mutableMapOf<Int, ObjectTraversal>()
        for((id, directAccess) in expected.directReads) {
            /**
             * We fully expect that for a direct read, the value we are accessing is an int (and recall
             * that each buffer access path/type combination are unique within a calldata buffer)
             */
            directReads[id] = paths[directAccess.bufferAccessPath.nonIndexed()]
                ?.get(HeapType.Int)
                ?.consumeToObjectPath(argRoots = arg, buffer = directAccess.bufferAccessPath)
                ?.traversal ?: return err {
                "Failed to resolve direct read $id, ${directAccess.bufferAccessPath.nonIndexed()}"
            }
        }
        /**
         * Finally, record that when reading from a constant, scalarized calldata offset, that location
         * should correspond to the synthetic argument name generated by [ArgNodeManager]
         */
        val primitiveBinding = expected.primitive.associateWith { arg.variableForRoot(it) }
        return ABICalleeBinding(
            decode = decodeBinding.mapValues { it.value.traversal },
            callSiteUse = callSiteBinding,
            argNames = arg.toArgNames(),
            directReads = directReads,
            primitiveBinding = primitiveBinding,
            initialization = initializationMap
        ).toLeft()
    }

    private fun computeInitializationMap(decodeBinding: Map<Int, BindingTraversal>): Either<Map<UnindexedPartition, PartitionLike<*>>, () -> String> {
        val initMapping = mutableMapOf<UnindexedPartition, PartitionLike<*>>()

        for((_, b) in decodeBinding) {
            val callerPart = b.sourcePointer
            val calleePart = b.outputPointer
            if(!computePartitionIsomorphism(src = callerPart, dst = calleePart, initMapping)) {
                return {
                    "Failed to compute partition isomorphism, src = $callerPart, dst = $calleePart, initMap = $initMapping"
                }.toRight()
            }
        }
        return initMapping.toLeft()
    }

    private fun computePartitionIsomorphism(src: IndexedAbstractPointer, dst: UnindexedTraversal, iso: MutableMap<UnindexedPartition, PartitionLike<*>>) : Boolean {
        for((fld, _) in dst.toAbstractObject()) {
            val (dPart, dstNxt) = dst.deref(fld) ?: return false
            val (sPart, srcNext) = src.deref(fld) ?: return false
            if (dPart !in iso) {
                iso[dPart] = sPart
            } else if (iso[dPart] != sPart) {
                return false
            }
            if(!computePartitionIsomorphism(src = srcNext, dst = dstNxt, iso)) {
                return false
            }
        }
        return true
    }

    /**
     * Traverse the type [ty], beginning at [curr], placing the buffer access paths of its contents into
     * [output].
     *
     * *Important*: If [ty] is dynamic, [curr] will already be deref'd. In other words, it is the responsibility of
     * callers to put [ty] into [output] at the (Deref-less) buffer access path.
     */
    private fun typesAtPath(
        curr: ObjectTraversalConstructor,
        ty: HeapType,
        output: MutableMap<DecoderAnalysis.BufferAccessPath, MutableMap<HeapType, ObjectTraversalConstructor>>
    ) : Boolean {
        check(!ty.isDynamic() || curr is ObjectTraversalConstructor.Deref)
        output.computeIfAbsent(curr.toBufferPath()) {
            mutableMapOf()
        }.put(ty, curr)
        when(ty) {
            is HeapType.Array -> {
                val length = ObjectTraversalConstructor.ArrayLength(curr)
                val elems = ObjectTraversalConstructor.ArrayElem(curr, EVM_WORD_SIZE)
                /**
                 * The elements (of type [ty].elementType) live conceptually as an element of the parent array.
                 * The deref/offset below is an "implementation detail" to give the location of the values
                 * that make up elements.
                 */
                output.computeIfAbsent(length.toBufferPath()) { mutableMapOf() }.put(HeapType.Int, length)
                output.computeIfAbsent(elems.toBufferPath()) { mutableMapOf() }.put(ty.elementType, elems)
                val next = if(ty.elementType.isDynamic()) {
                    ObjectTraversalConstructor.Deref(
                        ObjectTraversalConstructor.Offset(
                            offset = BigInteger.ZERO,
                            parent = elems,
                            fields = listOf()
                        )
                    )
                } else {
                    ObjectTraversalConstructor.Offset(
                        offset = BigInteger.ZERO, parent = elems, fields = listOf()
                    )
                }
                return typesAtPath(next, ty.elementType, output)
            }
            HeapType.ByteArray -> {
                val elem = ObjectTraversalConstructor.Offset(
                    parent = ObjectTraversalConstructor.ArrayElem(
                        curr,
                        BigInteger.ONE
                    ),
                    offset = BigInteger.ZERO,
                    fields = listOf()
                )
                output.computeIfAbsent(
                    elem.toBufferPath()
                ) { mutableMapOf() }.put(HeapType.Int, elem)
                return true
            }
            HeapType.EmptyArray -> return true
            HeapType.Int -> return true
            is HeapType.OffsetMap -> {
                for((offs, fTy) in ty.fieldTypes) {
                    /**
                     * Extend the physical offset, but record that the "single step" offset might correspond
                     * to multiple possible fields. For example, field x.a.b.c in
                     * struct X {
                     *    A a;
                     *  }
                     *  struct A { B b }; struct B { uint c; }
                     *
                     *  lives at phsyical offset 0, but corresponds to traversal of the logical fields 0, 0, 0
                     */
                    val withOffs = if (curr is ObjectTraversalConstructor.Offset) {
                        curr.copy(offset = curr.offset + offs, fields = curr.fields + offs)
                    } else {
                        ObjectTraversalConstructor.Offset(parent = curr, offset = offs, listOf(offs))
                    }
                    val traversal = if(fTy.isDynamic()) {
                        ObjectTraversalConstructor.Deref(withOffs)
                    } else {
                        withOffs
                    }
                    if(!typesAtPath(traversal, fTy, output)) {
                        return false
                    }
                }
                return true
            }
            is HeapType.TVar -> return false
        }
    }
}
