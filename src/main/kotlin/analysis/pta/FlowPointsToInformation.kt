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

package analysis.pta

import analysis.CmdPointer
import analysis.LTACCmd
import analysis.TACCommandGraph
import analysis.alloc.AllocationAnalysis
import analysis.alloc.AllocationInformation
import analysis.numeric.IntValue
import datastructures.stdcollections.*
import utils.hashObject
import utils.monadicFold
import utils.monadicMap
import utils.uniqueOrNull
import vc.data.TACCmd
import vc.data.TACKeyword
import vc.data.TACMeta
import vc.data.TACSymbol
import java.math.BigInteger
import java.util.*
import java.util.stream.Collector
import java.util.stream.Collectors
import java.util.stream.Stream

/**
 * The encapsulation of the points to information computed by the [PointsToAnalysis].
 */
class FlowPointsToInformation(
    val pta: PointsToAnalysis,
    private val graph: TACCommandGraph,
    override val allocationInformation: AllocationInformation,
    override val isCompleteSuccess: Boolean
) : IPointsToInformation, AbstractGarbageCollection, WithScratchPointer, WithSummaryInformation {
    private object EmptyLengthField : PTANode { override fun hashCode() = hashObject(this) }
    private object BigMemoryField : PTANode { override fun hashCode() = hashObject(this) }
    private object TransientNode : PTANode {
        override fun hashCode(): Int {
            return hashObject(this)
        }
    }

    sealed class Nodes : PTANode {
        sealed class ValueNode : Nodes() {
            data class StructObject(val v: AllocationSite) : ValueNode()
            data class ArrayObject(val v: AllocationSite) : ValueNode()
            object EmptyArray : ValueNode() { override fun hashCode() = hashObject(this) }
        }
        sealed class Field : Nodes() {
            data class StructField(val v: AllocationSite, val offset: BigInteger) : Field(), StructFieldNode {
                override val parentNode: PTANode
                    get() = ValueNode.StructObject(v)
            }
            data class ArrayElement(val v: AllocationSite, val elemSize: BigInteger) : Field(), ArrayElementNode {
                override val parentNode: PTANode
                    get() = ValueNode.ArrayObject(v)
            }
            object ScratchBase : Field(), ArrayLikeDataNode { override fun hashCode() = hashObject(this) }
            data class ArrayLengthField(val v: AllocationSite) : Field()
            data class ConcreteMemoryField(val v: Int) : Field()
            data class SpillField(val v: SpillLocation) : Field()
        }
    }

    private sealed class TypingKey {
        data class ArrayElem(val obj: AllocationSite) : TypingKey()
        data class StructField(val obj: AllocationSite, val offset: BigInteger) : TypingKey()
    }

    private val groupingBy : Collector<Pair<TypingKey, HeapType?>, *, Map<TypingKey, Optional<HeapType?>>> = Collectors.groupingBy({ it: Pair<TypingKey, HeapType?> ->
        it.first
    },
            Collectors.mapping({ it: Pair<TypingKey, HeapType?> ->
                it.second
            }, Collectors.filtering({
                it != null
            }, Collectors.reducing { a, b ->
                if (a == null || b == null) {
                    null
                } else if (!b.checkCompatibility(a)) {
                    null
                } else {
                    b.tryJoin(a)
                }
            })))

    private val globalTyping = pta.results.entries.parallelStream().flatMap { (_, v) ->
        Stream.concat(
            v.pointsToState.h.arraySpace.entries.stream().map {
                TypingKey.ArrayElem(it.key.addr) to when(val block = it.value.block) {
                    is ArrayBlock.Array -> block.elementType(v.pointsToState.h)
                    ArrayBlock.ByteArray -> HeapType.Int
                }
            },
            v.pointsToState.h.blockSpace.entries.stream().flatMap {
                it.value.block.fieldTypes.toMap(v.pointsToState.h).entries.stream().map { (offs, ty) ->
                    TypingKey.StructField(it.key.addr, offs) to ty
                }
            }
        )
    }.sequential().collect(groupingBy).mapValues {
        it.value.orElse(null)
    }

    private fun HeapType.mergeOrNull(o: HeapType?) : HeapType? = if(o == null) {
        this
    } else {
        o.takeIf { checkCompatibility(this) }?.join(this)
    }

    private fun PointsToDomain.extractFieldPointer(f: FieldAccess) : WritablePointsToSet? {
        val toRet = mutableListOf<PTANode>()
        var strong = true
        var ty : HeapType? = null
        for(p in f.blockAddr) {
            val blk = this.pointsToState.h[p]!!
            strong = toRet.isEmpty() && !blk.summary && strong
            toRet.add(Nodes.Field.StructField(
                offset = f.offset,
                v = p.addr
            ))
            ty = globalTyping[TypingKey.StructField(p.addr, f.offset)]?.mergeOrNull(ty) ?: return null
        }
        return WritableSet(
            nodes = toRet,
            rootType = ty ?: return null,
            updateType = if(strong) { WritablePointsToSet.UpdateType.STRONG } else { WritablePointsToSet.UpdateType.WEAK }
        )
    }

    private fun <T, U> Iterable<Pair<HeapType?, T>>.withCoherentType(f: (HeapType, Iterable<T>) -> U) : U? {
        return this.unzip().let { (pts, nodes) ->
            pts.monadicFold { f1, f2 ->
                if(f1.checkCompatibility(f2)) {
                    f1.join(f2)
                } else {
                    null
                }
            }?.let { t ->
                f(t, nodes)
            }
        }
    }

    /**
     * Points to set indicating this is a fake write of 0 that is part of initialization. The node we use [TransientNode]
     * is chosen to never overlap with others.
     */
    private val transientPointsToSet = object : WritablePointsToSet {
        override fun strongestUpdate(): WritablePointsToSet.UpdateType {
            return WritablePointsToSet.UpdateType.WEAK
        }

        override fun mayAlias(v: IPointsToSet): Boolean {
            return v.nodes.contains(TransientNode)
        }

        override fun mustAlias(v: IPointsToSet): Boolean {
            return false
        }

        override val nodes: Collection<PTANode>
            get() = listOf(TransientNode)
        override val type: IPointsToSet.Type
            get() = IPointsToSet.Type.COMPILER

    }

    override fun fieldNodesAt(where: CmdPointer, v: TACSymbol.Var): WritablePointsToSet? {
        return pta.results[where]?.let { dom ->
            val heap = dom.pointsToState.h
            dom.pointsToState.store[v]?.tryResolvePointer()?.let inner@{ vPtr ->
                when(vPtr) {
                    is ScratchPointer -> {
                        val offset = dom.arrayState[v]?.let { it as? ArrayStateAnalysis.Value.ScratchPointer }?.index ?:
                            throw IllegalStateException("Confusion in reduced product at $where for $v")
                        IndexableSet(
                            index = offset,
                            elementSize = BigInteger.ONE,
                            isStrongBase = true,
                            nodes = listOf(Nodes.Field.ScratchBase),
                            type = IPointsToSet.Type.INT
                        )
                    }
                    is NullablePointer -> null
                    INT -> {
                        if(heap.ignoreNextZeroWrite != null) {
                            return@inner if(heap.ignoreNextZeroWrite.sort is AllocationAnalysis.Alloc.ConstBlock) {
                                transientPointsToSet
                            } else if(heap.ignoreNextZeroWrite.sort is AllocationAnalysis.WithElementSize){
                                IndexableSet(
                                    index = IntValue.Nondet,
                                    elementSize = heap.ignoreNextZeroWrite.sort.getElementSize(),
                                    isStrongBase = false,
                                    nodes = listOf(Nodes.Field.ArrayElement(
                                        v = AllocationSite.Explicit(heap.ignoreNextZeroWrite),
                                        elemSize = heap.ignoreNextZeroWrite.sort.getElementSize()
                                    )),
                                    type = IPointsToSet.Type.COMPILER
                                )
                            } else {
                                null
                            }
                        }
                        val cmd = (graph.elab(where).cmd as? TACCmd.Simple.LongAccesses)?.accesses ?: return@inner null
                        val readAmount = cmd.singleOrNull {
                            it.offset == v && !it.isWrite && TACMeta.EVM_MEMORY in it.base.meta
                        } ?: return@inner null
                        val srcVal = dom.arrayState[v] as? ArrayStateAnalysis.Value.EndTracking ?: return@inner null
                        check(srcVal is ArrayStateAnalysis.WithIndexVars) {
                            "Invariant broken, have $srcVal which is EndTracking, but not a WithIndexVars"
                        }
                        if(!srcVal.untilEnd.any {
                            it.ops.any {
                                it == readAmount.length
                            }
                        }) {
                            return@inner null
                        }
                        srcVal.arrayPtr.monadicMap { arrVar ->
                            dom.pointsToState.store[arrVar] as? Pointer.ArrayPointer
                        }?.flatMap {
                            it.v
                        // if we are reading anything, it has to be from a "real" array
                        }?.filterIsInstance<ArrayAbstractLocation.A>()?.let {
                            arrayElementNodes(
                                it,
                                srcVal.constIndex?.let(IntValue.Companion::Constant) ?: IntValue.Nondet,
                                where = where,
                                v = v,
                                heap = dom.pointsToState.h
                            )
                        }
                    }
                    is Pointer.BlockPointerBase,
                    is Pointer.BlockPointerField -> {
                        dom.extractFieldPointer(vPtr as FieldAccess)
                    }
                    is Pointer.BlockPointerBaseAmbiguous -> {
                        if(vPtr.isResolvedArray()) {
                            null
                        } else {
                            dom.extractFieldPointer(vPtr as FieldAccess)
                        }
                    }
                    is Pointer.ConstSizeArrayElemPointer -> {
                        vPtr.v.flatMap { addr ->
                            heap[addr]!!.block.let { block ->
                                block.m.keys.map {
                                    block.fieldTypes[it, heap] to Nodes.Field.StructField(v = addr.addr, offset = it)
                                }
                            }
                        }.withCoherentType { ty, nodes ->
                            WritableSet(
                                nodes = nodes.toList(),
                                rootType = ty,
                                updateType = WritablePointsToSet.UpdateType.WEAK
                            )
                        }
                    }
                    is Pointer.ArrayPointer -> {
                        val (non, empty) = vPtr.v.partition {
                            it is ArrayAbstractLocation.A
                        }
                        /* think about it */
                        return generateArrayLengthField(
                            non.map { (it as ArrayAbstractLocation.A).addr },
                            structAliases = empty.filterIsInstance<ArrayAbstractLocation.StructAlias>().map {
                                it.addr.addr
                            },
                            includeEmptyLengthField = empty.isNotEmpty()
                        )
                    }
                    is Pointer.ArrayElemStart -> {
                        val seq = vPtr.v
                        arrayElementNodes(seq, IntValue.Constant(BigInteger.ZERO), heap, v, where)
                    }
                    is Pointer.ArrayElemPointer -> {
                        val x = dom.arrayState[v]?.let { it as? ArrayStateAnalysis.Value.ElementPointer } ?: throw IllegalStateException("Inconsistency in reduced product")
                        arrayElementNodes(vPtr.v, x.index, dom.pointsToState.h, v, where)
                    }
                    is InitializationPointer.ArrayInitPointer -> {
                        arrayInitToWriteNode(vPtr, dom, v)
                    }
                    is InitializationPointer.BlockInitPointer -> {
                        dom.extractFieldPointer(vPtr)
                    }
                    is InitializationPointer.ByteInitPointer -> {
                        if(!vPtr.mayAdded) {
                            arrayLengthSet(listOf(vPtr.initAddr.inject()))
                        } else {
                            arrayInitToWriteNode(vPtr, dom, v, IPointsToSet.Type.INT)
                        }
                    }
                    is InitializationPointer.StaticArrayInitPointer -> {
                        heap[vPtr.address]!!.block.let { block ->
                            block.m.keys.map {
                                check(globalTyping[TypingKey.StructField(vPtr.initAddr.inject(), it)]?.let { expect ->
                                    block.fieldTypes[it, heap]?.tryResolve()?.checkCompatibility(expect)
                                } == true) {
                                    "Expected ${globalTyping[TypingKey.StructField(vPtr.initAddr.inject(), it)]}, got:  ${block.fieldTypes[it, heap]}"
                                }
                                block.fieldTypes[it, heap] to Nodes.Field.StructField(v = vPtr.initAddr.inject(), offset = it)
                            }
                        }.withCoherentType { ty, nodes ->
                            WritableSet(
                                rootType = ty,
                                nodes = nodes.toList(),
                                updateType = WritablePointsToSet.UpdateType.WEAK
                            )
                        }
                    }
                }
            } ?: if(heap.concreteSpace.isNotEmpty() && dom.boundsAnalysis[v]?.tryResolveAsInt() is QualifiedInt) {
                fieldNodesAt(where, dom.boundsAnalysis[v]!!.expectInt().x)
            } else {
                null
            }
        }
    }

    private fun arrayElementNodes(
        seq: Iterable<ArrayAbstractLocation.A>,
        indAbstraction: IntValue,
        heap: AbstractHeap,
        v: TACSymbol.Var,
        where: CmdPointer
    ): IndexableSet? {
        data class IntermediateNode(val node: Nodes.Field.ArrayElement, val strong: Boolean)
        return seq.monadicMap { aLoc ->
            val addr = aLoc.addr
            heap[aLoc]?.let { blk ->
                val elemType = globalTyping[TypingKey.ArrayElem(addr)].let { ty ->
                    if (ty == null && !mustBeEmptyArray(addr)) {
                        throw java.lang.IllegalStateException("Could not infer type of elements $aLoc for (non-empty?) array $v @ $where")
                    }
                    ty
                }
                check(elemType == null || extractArrayType(blk, heap)?.checkCompatibility(elemType) == true) {
                    "Unexpected heap type ${elemType}, expected ${extractArrayType(blk, heap)} of $aLoc @ $where"
                }
                elemType to IntermediateNode(
                    node = Nodes.Field.ArrayElement(v = addr, elemSize = addr.getElementSize()?.toConcrete() ?: return@monadicMap null),
                    strong = !blk.summary
                )
            }
        }?.withCoherentType { heapType, nodes ->
            val elemSize = nodes.map { it.node.elemSize }.uniqueOrNull() ?: return@withCoherentType null
            val isStrong = nodes.singleOrNull()?.strong == true
            val addresses = nodes.map { it.node }
            IndexableSet(
                nodes = addresses,
                index = indAbstraction,
                type = heapType.toPTType(),
                isStrongBase = isStrong,
                elementSize = elemSize
            )
        }
    }

    override fun fieldNodesAt(where: CmdPointer, v: IPointsToSet, offset: BigInteger): WritablePointsToSet? {
        return v.nodes.monadicMap {
            (it as? Nodes.ValueNode.StructObject)?.v
        }?.monadicMap {
            globalTyping[TypingKey.StructField(it, offset)]?.to(Nodes.Field.StructField(
                offset = offset,
                v = it
            ))
        }?.withCoherentType { fTy, nodes ->
            WritableSet(
                rootType = fTy,
                nodes = nodes.toList(),
                updateType = nodes.singleOrNull()?.let {
                    val heap = pta.results[where]?.pointsToState?.h
                    if(heap?.get(L(it.v))?.summary == false) {
                        WritablePointsToSet.UpdateType.STRONG
                    } else {
                        WritablePointsToSet.UpdateType.WEAK
                    }
                } ?: WritablePointsToSet.UpdateType.WEAK
            )
        }
    }

    override fun fieldNodesAt(where: CmdPointer, c: TACSymbol.Const): WritablePointsToSet? = fieldNodesAt(where, IntValue.Constant(c.value))

    private fun fieldNodesAt(where: CmdPointer, range: IntValue): WritablePointsToSet? {
        return pta.results[where]?.let { ptd ->

            // First check if this is a spill access
            with(pta.pointerAnalysis) {
                range.asSpillLocation()?.let {
                    return WritableSet(
                        nodes = listOf(Nodes.Field.SpillField(it)),
                        updateType = WritablePointsToSet.UpdateType.STRONG,
                        rootType = ptd.pointsToState.h.spillSpace[it]?.getType(ptd.pointsToState.h) ?: HeapType.Int
                    )
                }
            }

            ptd.pointsToState.h.concreteSpace.ranges(range).ifEmpty {
                null
            }?.let { nodes ->
                if(nodes.size == 1 && nodes.single().let {
                    it.range.lb <= range.lb
                }) {
                    val nodeRange = nodes.single().range
                    return IndexableSet(
                        index = range.copy(
                            lb = range.lb - nodeRange.lb,
                            ub = range.ub - nodeRange.lb
                        ),
                        elementSize = BigInteger.ONE,
                        isStrongBase = true,
                        nodes = listOf(Nodes.Field.ConcreteMemoryField(nodes.single().ordinal!!)),
                        type = IPointsToSet.Type.INT
                    )
                }
                WritableSet(
                    nodes = nodes.map { Nodes.Field.ConcreteMemoryField(it.ordinal!!) },
                    rootType = HeapType.Int,
                    updateType = WritablePointsToSet.UpdateType.WEAK
                )
            }
        }
    }

    override fun fieldNodesAt(where: CmdPointer, s: TACSymbol): WritablePointsToSet? {
        return when (s) {
            is TACSymbol.Const -> fieldNodesAt(where, s)
            is TACSymbol.Var -> fieldNodesAt(where, s)
        }
    }

    private fun arrayLengthSet(vPtr: List<AllocationSite>, structAlias: List<AllocationSite> = listOf()) = object : WritablePointsToSet {
        override fun strongestUpdate(): WritablePointsToSet.UpdateType = WritablePointsToSet.UpdateType.INVALID

        /* trivial implementations */
        override fun mayAlias(v: IPointsToSet): Boolean = true

        override fun mustAlias(v: IPointsToSet): Boolean = false

        override val nodes: Collection<PTANode> = vPtr.map(Nodes.Field::ArrayLengthField) + structAlias.map {
            Nodes.Field.StructField(it, BigInteger.ZERO)
        }
        override val type: IPointsToSet.Type
            get() = IPointsToSet.Type.COMPILER

    }

    private fun setOfHeapValue(v: HeapValue, pts: PointsToDomain) : IPointsToSet? {
        return when (v) {
            is INT -> {
                null
            }
            is Pointer.BlockPointerBase -> {
                ValuePointsToSet(
                    v.blockAddr.map {
                        Nodes.ValueNode.StructObject(it.addr)
                    },
                    rootType = v.getType(pts.pointsToState.h),
                    anySummary = v.blockAddr.any {
                        pts.pointsToState.h[it]?.summary != false
                    }
                )
            }
            is Pointer.BlockPointerBaseAmbiguous -> {
                if (v.isResolvedArray()) {
                    ValuePointsToSet(
                        nodes = listOf(Nodes.ValueNode.EmptyArray),
                        anySummary = false,
                        rootType = v.getType(pts.pointsToState.h)
                    )
                } else {
                    ValuePointsToSet(
                        v.blockAddr.map {
                            Nodes.ValueNode.StructObject(it.addr)
                        },
                        rootType = v.getType(pts.pointsToState.h),
                        anySummary = v.blockAddr.any {
                            pts.pointsToState.h[it]?.summary != false
                        }
                    )

                }
            }
            is Pointer.ArrayPointer -> {
                val taggedNodes = v.v.map {
                    when (it) {
                        is ArrayAbstractLocation.A -> (pts.pointsToState.h[it]?.summary == false) to Nodes.ValueNode.ArrayObject(
                            it.addr
                        )
                        is ArrayAbstractLocation.StructAlias -> false to Nodes.ValueNode.EmptyArray
                        ArrayAbstractLocation.EMPTY_ARRAY -> false to Nodes.ValueNode.EmptyArray
                    }
                }
                val (strong, nodes) = taggedNodes.unzip()
                ValuePointsToSet(
                    nodes = nodes,
                    anySummary = strong.any { !it },
                    rootType = v.getType(pts.pointsToState.h)
                )
            }
            is UnkPointsTo -> {
                (v.tryResolve() as HeapValue).let {
                    if(it is UnkPointsTo) {
                        it.expectInt()
                    } else {
                        it
                    }
                }.let { setOfHeapValue(it, pts = pts) }
            }
        }
    }

    private fun joinHeap(a: HeapValue, b: HeapValue) : HeapValue? {
        return try {
            a.strictJoin(b)
        } catch(_: TypeMismatchFailureException) {
            null
        }
    }

    override fun contentsOf(where: CmdPointer, set: WritablePointsToSet): IPointsToSet? {
        return pta.results[where]?.let { dom ->
            set.nodes.monadicMap {
                it as? Nodes.Field
            }?.monadicMap {
                when(it) {
                    is Nodes.Field.ArrayElement -> dom.pointsToState.h[ArrayAbstractLocation.A(it.v)]?.block?.let {
                        when(it) {
                            is ArrayBlock.Array -> it.elem
                            ArrayBlock.ByteArray -> INT
                        }
                    }
                    Nodes.Field.ScratchBase -> INT
                    is Nodes.Field.StructField -> dom.pointsToState.h[L(it.v)]?.block?.m?.get(it.offset)
                    is Nodes.Field.ArrayLengthField -> INT
                    is Nodes.Field.ConcreteMemoryField -> INT
                    is Nodes.Field.SpillField -> dom.pointsToState.h.spillSpace[it.v]
                }
            }?.monadicFold(this::joinHeap)?.let {
                setOfHeapValue(it, dom)
            }
        }
    }

    override fun reachableObjects(where: CmdPointer, v: TACSymbol.Var): IPointsToSet? {
        return pta.results[where]?.let { dom ->
            dom.pointsToState.store[v]?.let {
                it as? HeapValue
            }?.let { setOfHeapValue(it, dom) }
        }
    }

    override fun reachableObjects(where: CmdPointer, v: IPointsToSet, offset: BigInteger): IPointsToSet? {
        return pta.results[where]?.let { dom ->
            v.nodes.monadicMap {
                it as? Nodes.ValueNode.StructObject
            }?.monadicMap {
                dom.pointsToState.h[L(it.v)]?.block?.m?.get(offset)
            }?.monadicFold(this::joinHeap)?.let {
                setOfHeapValue(v = it, pts = dom)
            }
        }
    }

    override fun lengthFieldAt(where: CmdPointer, set: IPointsToSet): IPointsToSet? {
        var mayBeEmptyArray = false
        val locations = mutableListOf<AllocationSite>()
        val structAliasLocations = mutableListOf<AllocationSite>()
        for(v in set.nodes) {
            val narrowed = (v as? Nodes.ValueNode) ?: return null
            when(narrowed) {
                is Nodes.ValueNode.ArrayObject -> locations.add(narrowed.v)
                Nodes.ValueNode.EmptyArray -> mayBeEmptyArray = true
                is Nodes.ValueNode.StructObject -> {
                    if(pta.results[where]?.pointsToState?.h?.let {
                        it[L(narrowed.v)]?.block?.mustNotBeEmptyArray == false
                    } == true) {
                        structAliasLocations.add(narrowed.v)
                    } else {
                        return null
                    }
                }
            }
        }
        return generateArrayLengthField(locations, structAliases = structAliasLocations, includeEmptyLengthField = mayBeEmptyArray)
    }

    private fun generateArrayLengthField(properArrays: List<AllocationSite>, structAliases: List<AllocationSite>, includeEmptyLengthField: Boolean) : WritablePointsToSet {
        val arrayLengthSet = arrayLengthSet(properArrays, structAliases)
        return if(!includeEmptyLengthField) {
            arrayLengthSet
        } else {
            object : WritablePointsToSet by arrayLengthSet {
                override val nodes: Collection<PTANode>
                    get() = arrayLengthSet.nodes + EmptyLengthField
            }
        }

    }

    override fun arrayFieldAt(where: CmdPointer, v: IPointsToSet): WritablePointsToSet? {
        return v.nodes.monadicMap {
            (it as? Nodes.ValueNode)?.takeIf {
                it !is Nodes.ValueNode.StructObject
            }
        }?.mapNotNull {
            it as? Nodes.ValueNode.ArrayObject
        }?.let {
            val ty = it.monadicMap {
                globalTyping[TypingKey.ArrayElem(it.v)]
            }?.monadicFold { a, b -> a.mergeOrNull(b) } ?: return@let null
            val elemSize = it.monadicMap {
                it.v.getElementSize()?.toConcrete()
            }?.uniqueOrNull() ?: return@let null
            IndexableSet(
                nodes = it.map {
                    Nodes.Field.ArrayElement(
                        v = it.v,
                        elemSize = elemSize
                    )
                },
                index = IntValue.Nondet,
                elementSize = elemSize,
                type = ty.toPTType(),
                isStrongBase = it.singleOrNull()?.v?.let { allocSite ->
                    pta.results[where]?.let { pointerDomain ->
                        pointerDomain.pointsToState.h[ArrayAbstractLocation.A(addr = allocSite)]?.let { obj ->
                            !obj.summary
                        }
                    }
                } == true
            )
        }
    }

    override fun reachableArrayElements(where: CmdPointer, v: IPointsToSet): IPointsToSet? {
        return pta.results[where]?.let { dom ->
            v.nodes.filter {
                it !is Nodes.ValueNode.EmptyArray
            }.monadicMap {
                it as? Nodes.ValueNode.ArrayObject
            }?.monadicMap {
                when(val x = dom.pointsToState.h[ArrayAbstractLocation.A(it.v)]?.block) {
                    is ArrayBlock.Array -> x.elem
                    ArrayBlock.ByteArray -> INT
                    null -> null
                }
            }?.monadicFold(this::joinHeap)?.let {
                setOfHeapValue(it, pts = dom)
            }
        }
    }

    private fun extractArrayType(blk: AbstractObject<ArrayBlock>, h: AbstractHeap): HeapType? {
        return when (val arrBlock = blk.block) {
            is ArrayBlock.Array -> arrBlock.elementType(h)
            is ArrayBlock.ByteArray -> HeapType.Int
        }
    }

    private fun mustBeEmptyArray(v: AllocationSite) : Boolean {
        return v is AllocationSite.Explicit && when(v.alloc.sort) {
            is AllocationAnalysis.Alloc.ConstantArrayAlloc -> v.alloc.sort.constSize == BigInteger.ZERO
            is AllocationAnalysis.Alloc.ConstantStringAlloc -> v.alloc.sort.constLen == BigInteger.ZERO
            else -> false
        }
    }

    private fun AllocationAnalysis.AbstractLocation.inject() = AllocationSite.Explicit(this)

    private fun arrayInitToWriteNode(
        vPtr: InitializationPointer.LengthFieldInit,
        dom: PointsToDomain,
        v: TACSymbol.Var,
        ty : IPointsToSet.Type = globalTyping[TypingKey.ArrayElem(AllocationSite.Explicit(vPtr.initAddress.addr))]?.toPTType() ?: IPointsToSet.Type.UNKNOWN
    ): WritablePointsToSet {
        val asWrappedField = ArrayAbstractLocation.A(vPtr.initAddress.addr)
        val strongFlag = asWrappedField !in dom.pointsToState.h.arraySpace
        if(!vPtr.mayAdded) {
            return arrayLengthSet(listOf(vPtr.initAddress.addr.inject()))
        }
        val index = dom.arrayState[v]?.let { it as? ArrayStateAnalysis.Value.ElementPointer }?.index ?: IntValue.Nondet
        return IndexableSet(
            index = index,
            type = ty,
            elementSize = (vPtr.initAddress.addr.sort as AllocationAnalysis.WithElementSize).getElementSize(),
            isStrongBase = strongFlag,
            nodes = listOf(
                Nodes.Field.ArrayElement(
                    elemSize = (vPtr.initAddress.addr.sort as AllocationAnalysis.WithElementSize).getElementSize(),
                    v = vPtr.initAddress.addr.inject()
                )
            )
        )
    }

    override fun gcAt(where: LTACCmd): Set<PTANode> {
        if((where.cmd is TACCmd.Simple.AssigningCmd && where.cmd.lhs == TACKeyword.MEM64.toVar()) || where.cmd is TACCmd.Simple.CallCore || where.cmd is TACCmd.Simple.LogCmd) {
            if(where.cmd is TACCmd.Simple.CallCore && where.cmd.inOffset is TACSymbol.Const) {
                pta.results[where.ptr]?.pointsToState?.h?.takeIf {
                    it.concreteSpace.isNotEmpty()
                }?.concreteSpace?.findIntersection(IntValue.Constant(where.cmd.inOffset.value))?.singleOrNull()?.let { r ->
                    Nodes.Field.ConcreteMemoryField(r.find().ordinal!!)
                }?.let { return setOf(it) }
            }
            return setOf(Nodes.Field.ScratchBase)
        } else {
            return setOf()
        }
    }

    override fun <T> query(q: PointsToQuery<T>) : T? {
        return q.compute(
            pta = pta,
            graph = graph,
            pts = this
        )
    }

    override val scratchPointer: PTANode
        get() = Nodes.Field.ScratchBase
}
