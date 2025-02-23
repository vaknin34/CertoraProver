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

import allocator.Allocator
import allocator.GenerateRemapper
import allocator.GeneratedBy
import analysis.CommandWithRequiredDecls
import com.certora.collect.*
import datastructures.stdcollections.*
import instrumentation.transformers.MemoryPartition
import tac.CallId
import tac.Tag
import utils.KSerializable
import vc.data.*

/**
 * A type that "acts" like a partition, indexed by a [CallIdx] (in the sense of a call index).
 * These can either be [ConcretePartition] or [TransientPartition] objects. Each object
 * provides a way to "initialize" a [tac.Tag.ByteMap] to be equal to this partition (with [toInitializationTerm]),
 * and a way to read values out of the partition at some index (with [selectCommand]). The numeric id of the partition
 * (which, in practice, comes from the [Allocator.Id.MEMORY_PARTITION] sequence) is given by [partitionId],
 * and the call index by [callIdx]. This call index serves the same role as [TACSymbol.Var.callIndex];
 * multiple inlinings of the same method can duplicate partition ids. The pair of [partitionId] and [callIdx]
 * is thus distinct.
 */
sealed interface PartitionLike<CallIdx> {
    /**
     * Return a term that, when used as the [vc.data.TACCmd.Simple.AssigningCmd.AssignExpCmd.rhs] of an assignment
     * to a variable of type [tac.Tag.ByteMap] will initialize that ByteMap to be (initially) equal to this partition.
     */
    fun toInitializationTerm(): TACExpr

    /**
     * Return a series of commands that writes into [lhs] the value read out of this partition at location [loc].
     */
    fun selectCommand(lhs: TACSymbol.Var, loc: TACSymbol) : CommandWithRequiredDecls<TACCmd.Simple>

    /**
     * The partition id.
     */
    val partitionId: Int

    /**
     * The call index.
     */
    val callIdx: CallIdx
}

/**
 * A concrete, fully materialized partition, representing an actual [tac.Tag.ByteMap] variable at
 * some call index (indeed, the type of [callIdx] is a [CallId]). This class is just a thin wrapper
 * around the variable which holds the partition variable with [partitionId] at [callIdx], which
 * is consistently generated via [MemoryPartition.partitionFor].
 *
 * XXX(jtoman): this is basically vestigial and should be removed at some point.
 */
@GenerateRemapper
@KSerializable
data class ConcretePartition(
    @GeneratedBy(Allocator.Id.MEMORY_PARTITION)
    override val partitionId: Int,
    @GeneratedBy(Allocator.Id.CALL_ID)
    override val callIdx: CallId
) : RemapperEntity<ConcretePartition>, PartitionLike<CallId> {
    override fun toInitializationTerm(): TACExpr {
        return toBaseMap().asSym()
    }

    override fun selectCommand(lhs: TACSymbol.Var, loc: TACSymbol): CommandWithRequiredDecls<TACCmd.Simple> {
        val base = toBaseMap()
        return CommandWithRequiredDecls(listOf(TACCmd.Simple.AssigningCmd.ByteLoad(
            lhs = lhs,
            loc = loc,
            base = base
        )), setOfNotNull(lhs, loc as? TACSymbol.Var, base))
    }

    fun toBaseMap(): TACSymbol.Var {
        return MemoryPartition.partitionFor(partitionId = partitionId, callIdx = callIdx)
    }
}

/**
 * A "transient" call id, which "forward" declares a call id before said call ids are assigned. The reason for
 * why this is necessary is complicated. The short answer is so-called "calldata passthroughs" means that decodes/direct reads
 * of an argument out of calldata in some `callee` need to reference memory that is *not* the immediate caller's memory.
 *
 * For example, consider the following scenario:
 * ```
 * struct A {
 *    uint x;
 *    B b;
 * }
 * struct B {
 *    uint[] array;
 * }
 * function caller(A memory a) {
 *    mid(a)
 * }
 *
 * function mid(A calldata a) {
 *    callee(a)
 * }
 *
 * function callee(A calldata a) {
 *    B memory b = a.b;
 * }
 * ```
 *
 * As with all inlining, under direct passing, the body of `callee` is inlined into `mid`, after which that function
 * is inlined into `caller`. The [TransientCallId] answers the question: "When inlining `caller` into `mid`, how do we
 * effect the read of field `b` when initializating the variable that holds the result of the decode operation?"
 *
 * Recall that when doing direct passing, we delete all of the code that performs the decode, in this case which
 * reads the values that make up the struct in calldata. We replace it with an expression that gives the "high-level"
 * value of the argument, and initialize the memory partitions in the callee with the partitions that hold the data
 * of the argument.
 *
 * In this example however, what memory partition do we read from when traversing the `b` field of `a`? Because `mid`
 * is just passing the data through, the partition holding the value of the field `b` doesn't "exist" in its memory space;
 * it exists in the function that called mid, i.e., caller. Even if we pass the actual partition ID through to inlining of callee
 * into mid, what [CallId] should we use for the ByteMap? It cannot be call index 0, because that (falsely) implies that
 * the memory is part of `mid`. Recall that when we inline `mid` into `caller`, we consistently remap all of the callids
 * that occur within the body of `mid`, including call index 0.
 *
 * Intuitively, we want some way of saying `tacM!k@eventual-id-of-caller`, where `k` is the partition
 * id which holds the field of `b`. One option would be to precompute the call ids assigned to each function, and use those.
 * However, this is a non-starter for two reasons. One: suppose that `caller` is the root of the inlining process. Then the
 * eventual-id-of-caller would just be 0, which, as discussed above, breaks when we inline `mid` into `caller`. However,
 * even if this is not the case, the automatic remapping of call-ids is still problematic. Suppose we knew, a priori, that
 * the instance of `caller` that contains the call to `mid` was assigned call index j. Further, suppose that
 * `caller` was separated from `callee` by an arbitrary number of calls to functions like `mid` which passthrough their calldata
 * arg. Then our inlining process would have to "remember" at each intermediate inlining to treat call index `j` specially
 * and *NOT* remap it. With multiple sources of calldata arguments, this bookkeeping becomes even more difficult.
 *
 * One other option would be to delay the instrumentation of the decode of `callee` until we inlined `mid` into `caller`.
 * However, this is complicated by intermediate passthroughs performing "partial" object traversals, e.g.,
 * ```
 * function mid(A calldata a) {
 *    callee(a.b)
 * }
 *
 * function callee(B calldata b) {
 *    uint[] memory x = b.array;
 * }
 * ```
 *
 * Here, the access of the `array` field is "spread" across two functions, the first access of field `b` in `mid`, and then
 * the read of the `array` field and decoding of the array in `callee`. Thus, instrumenting decodes becomes a nightmare
 * of stiching back up object accesses; e.g. attemping to recover that, at the decode in `callee`, we are actually
 * accessing caller's `a.b.array` field (which, again, is spread across the [ABIEncodeComplete] annotation in `mid` and the
 * [ABIDecodeComplete] annotation in `callee`).
 *
 * However, the idea of precomputing the call id assigned to `caller`, and then performing operations on the partitions at
 * that call index is actually *close* to what we want. We want some way to effect the memory operations that read the
 * `b` field of the calldata argument `a` in `caller`'s memory space, but cannot use any *concrete* call id as those
 * are automatically remapped by the [CoreTACProgram.createCopy] function. In other words, we want to "hide" the fact that
 * we're doing memory operations until the call id for caller has stabilized.
 *
 * Enter [TransientCallId] and the [TransientPartition]. Intuitively, a [TransientCallId] refers to
 * "an activation record that exists somewhere 'higher up' in the callstack, into which we will eventually be inlined'. Similarly,
 * a [TransientPartition] refers to "a memory partition that does not 'exist' yet, but is defined in some
 * method 'higher up' in the callstack".
 *
 * In other words, this allows us to refer to `caller`'s memory partitions in a way that is not interefered with by the
 * remapping. Further, we do *not* need to ultimatley know what `caller`'s eventual *concrete* call id will be.
 *
 * The way [TransientPartition] and [TransientCallId] works is as follows. Every inlining for a method node `m`
 * in the canonicalized tree of the [analysis.icfg.Inliner] is assigned a [TransientCallId], `t`. If `m` passes a reference typed argument
 * `a` to some callee, the abstract object layout of that argument (see [analysis.icfg.IndexedAbstractPointer]) and the [TransientCallId]
 * `t` is plumbed through to the decode point. That decoding operation is then effected using memory operations
 * on the [TransientPartition]'s indicated by the plumbed through [analysis.icfg.IndexedAbstractPointer]. Note that these
 * operations can happen arbitrarily "far away" from the method that passed the argument. Once `m` is fully processed
 * (that is, all its callees are inlined, and thus, all possible decodings of `a` have been seen),
 * the code for `m` is scanned for operations that operate on partitions with the transient id `t`. These
 * operations are then "materialized" into operations on actual bytemaps with call index 0. Note that this use
 * of call index 0 is safe, as once we are done processing the node with ID `t`, the memory space at call index 0
 * is indeed the memory space of the method which originally passed the reference typed argument. If `m` is
 * itself later inlined into another function, then these references to call index 0 will be properly
 * remapped to refer to the newly assigned call index for `m`.
 *
 * The actual "transient" memory operations are done using [TACBuiltInFunction]. Specifically
 * [TACBuiltInFunction.ReadTransientPartition] indicates that a value should be read from some (not yet materialized)
 * partition at a specific location, and [vc.data.TACBuiltInFunction.PartitionInitialize] indicates that a bytemap
 * should be initialized to be equal to the indicated (as yet unmaterialized) partition.
 *
 * To complete this discussion let us return to the extended example:
 * ```
 * function caller(A memory a) {
 *    mid(a);
 * }
 * function mid(A calldata a) {
 *    callee(a.b);
 * }
 *
 * function callee(B calldata b) {
 *    uint[] memory x = b.array;
 * }
 * ```
 * We first assign `caller` the transient id 17. We also know that `a` has an abstract object layout as follows (using
 * a modified notation of [analysis.icfg.IndexedAbstractPointer]):
 * ```
 * StructField(0) => {6}
 * StructField(32) => {7,
 *    StructField(0) => {8,
 *       ArrayElement(32) => {9},
 *       ArrayLength => {10}
 *   }
 * }
 * ```
 * Here the partitions are given using the unindexed partition id, that is, the value of the [optimizer.UNINDEXED_PARTITION]
 * meta. These are packaged up into an [analysis.icfg.IndexedAbstractPointer] and pushed through to `mid` and eventually
 * `callee` (the details of this are discussed in [analysis.icfg.ABICallConvention]). From direct passing,
 * we know that the variable which contains the pointer to the argument `a` in `mid` resides in some new variable, call it `abiArgA`.
 * Likewise, we know that the variable which holds the pointer to `b` in `callee` is some other variable, call it `abiArgB`.
 *
 * We first consider the inlining of `callee` into `mid` (as that happens first).  When instrumenting the *call* from `mid` to `callee`,
 * we have to effect the read of the field `b` from `abiArgA` to bind
 * to the high-level argument for `b` in `callee` (`abiArgB`). This is the struct field 32 of a, which the abstract object
 * layout indicates the partition index 7. The [analysis.icfg.IndexedAbstractPointer] that represents the argument `a` also
 * has the transient id for the partition, which is 17. Thus, we bind `abiArgB` as follows:
 * `abiArgB = ReadTransientPartition_17_7(abiArgA + 32)`
 * the `_17_7` are the "meta" args, indicating that we want to read the value out of this partition, as soon as the
 * partition is available.
 *
 * Further, within the body of `callee` we must effect the read of the `array` field, and bind it to the output of
 * the decode (which, for convenience, we will call `x`). Again, the abstract object layout plumbed through with
 * the [analysis.icfg.IndexedAbstractPointer] indicates that the first
 * field of the struct in `b` resides in partition `8`, with transient id 17, Thus, we effect the read with:
 * `x = ReadTransientPartition_17_8(abiArgB)`
 *
 * Finally, we need to initialize the partitions in `callee` that will hold the data for `x`. The [analysis.icfg.IndexedAbstractPointer]
 * indicates these are `9` and `10`, so we initialize the partitions in `callee` as follows:
 * ```
 * x_data_partition = PartitionInitialize_17_9()
 * x_length_partition = PartitionInitialize_17_10()
 * ```
 *
 * We then inline the body of `mid` (which now has these references to [vc.data.TACBuiltInFunction.PartitionInitialize]
 * and [vc.data.TACBuiltInFunction.ReadTransientPartition]) into `caller`. At this point, the inlining
 * process for `caller`, and thus, transient id 17, is done. The program is thus scanned for references to transient
 * id 17, and these references are replaced with "concrete" operations. Thus, the above snippets become:
 * ```
 * abiArgB = tacM!7@0[abiArgA + 32]
 * x = tacM!8@0[abiArgB]
 * x_data_partition = tacM!9@0
 * x_length_partition = tacM!10@0
 * ```
 *
 * The actual plumbing through of the abstract pointers, the generation of these transient partition operations,
 * and their materialization are described in [analysis.icfg.Inliner] and [analysis.icfg.ABICallConvention].
 */
@Treapable
@JvmInline
@KSerializable
value class TransientCallId(val transientId: Int)

/**
 * A representation of a transient partition with some
 * [partitionId] and (transient) call index [callIdx]. The terms generated by [toInitializationTerm]
 * and [selectCommand] use bifs, which are expected to be replaced later.
 */
data class TransientPartition(
    override val partitionId: Int,
    override val callIdx: TransientCallId
) : PartitionLike<TransientCallId> {
    /**
     * Initialize a byte map to be equal to this transient partition, by using the
     * [vc.data.TACBuiltInFunction.PartitionInitialize] bif.
     */
    override fun toInitializationTerm(): TACExpr {
        return TACExpr.Apply(
            TACBuiltInFunction.PartitionInitialize(
                partitionId = partitionId,
                transientId = callIdx
            ).toTACFunctionSym(),
            listOf(),
            Tag.ByteMap
        )
    }

    /**
     * Read out of a transient partition at [loc] by supplying [loc] as an argument to [vc.data.TACBuiltInFunction.ReadTransientPartition]
     * parameterized with the [partitionId] and [callIdx].
     */
    override fun selectCommand(lhs: TACSymbol.Var, loc: TACSymbol): CommandWithRequiredDecls<TACCmd.Simple> {
        return CommandWithRequiredDecls(listOf(
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = lhs,
                rhs = TACExpr.Apply(
                    TACBuiltInFunction.ReadTransientPartition(
                        partitionId = partitionId,
                        transientId = callIdx
                    ),
                    listOf(loc.asSym()),
                    Tag.Bit256
                )
            )
        ), setOfNotNull(lhs, loc as? TACSymbol.Var))
    }
}

