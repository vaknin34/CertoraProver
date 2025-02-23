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

import analysis.pta.abi.*
import datastructures.stdcollections.*


/**
 * Representation of an "abstract object layout" or "abstract memory layout", i.e.,
 * how fields of an object are assigned to different partitions (as is performed in the
 * [optimizer.OptimizeBasedOnPointsToAnalysis] optimizations). Recall that after partitioning,
 * objects do not exist as monolithic blocks, rather, the different fields of the object are spread across
 * different [tac.Tag.ByteMap]. Thus, when interpreting an access to a field of an object (e.g.,
 * any element of an array, the 2nd field of a struct, an array's length) it is imperative to know which [tac.Tag.ByteMap]
 * should be read from/stored to, i.e., the [vc.data.TACCmd.Simple.AssigningCmd.ByteLoad.base] to use. (Recall as well
 * that partitioning does *not* change the actual indices into memory arrays, simply the base of the memory operations).
 *
 * Thus, the abstract memory layout for a struct with 3 fields will (at least) indicate which three memory partitions
 * ([tac.Tag.ByteMap] instances) in which the *value* of those fields reside. Note that these partitions may not necessarily
 * be distinct. Further, the abstract object layout is _recursive_, if any of the fields in the above struct are themselves reference
 * types, the abstract object layout will include the information about the partitions which contain the values of those reachable fields.
 *
 * Thus, the abstract object/memory layout is a tree. For reference types (or objects, we use the term interchangeably),
 * there is one "child" node for each abstract field (thus, the "edge" in the abstract object to the
 * child is labeled with the abstract field). Note that we use "abstract fields" because all elements of an array
 * are represented using a summary field node. This child node contains at least one piece of information: the partition (i.e.,
 * ByteMap) which holds the value of that field for the given object. If the field itself holds a reference type,
 * then that child node may itself have labelled children. Note that a partition may be mentioned multiple times
 * within an abstract layout due to, e.g., aliasing. Note that the root node has no partition information, as the "top level"
 * value lives in a variable.
 *
 * For example, suppose we have the following type definitions:
 * ```
 *  struct A {
 *    uint a;
 *    B b;
 * }
 *
 * struct B {
 *    uint[] array;
 *    uint c;
 * }
 * ```
 * And we have a variable `a` known to point to an instance of A. Then this object with have the following abstract layout:
 * ```
 * StructField(0) => {tacM!3}
 * StructField(32) =>
 *     {tacM!4,
 *        StructField(0) =>
 *           {tacM!5,
 *              ArrayElement(32) => {tacM!6},
 *              ArrayLength => {tacM!7}
 *           }
 *       StructField(32) => {tacM!8}}
 * ```
 *
 * The identifiers `tacM!k` are arbitrary (and, as seen below, the choice of partition representation depends on context).
 * This abstract layout can be interpreted as follows. To retrieve the value
 * of `a.b.array[5]` we first consult the label for `StructField(32)` (i.e., the second field in the struct), which
 * gives `{tacM!4,...}. This
 * tells us that the bytemap that holds the value of field `b` is `tacM!4`. To retrieve this value, we would need to read
 * tacM!4 at index `a + 32`. We then continue traversal, following `StructField(0)`, that is, the *first* field in the
 * struct of type B reached by following field `b`. We find `{tacM!5,...}`, which as above, indicates that the partition
 * which holds the value of field `b` is `tacM!5`. Then we read the first field of the intermediate struct read above,
 * i.e. `tacM!5[tacM!4[a + 32]]`. The result of this read is itself a pointer, this time to a struct. Finally, we consult
 * the node for the label `ArrayElement(32)`, which gives `tacM!6`. Thus, once we compute the memory offset
 * for element `5`, we will read that from the `tacM!6` bytemap. In our case, that offset is:
 * `tacM!5[tacM!4[a + 32]] + 32 + 32 * 5`, which then becomes the index to a read out of `tacM!6`.
 *
 * We strongly assume Solidity's convention of non-cyclic object graphs, allowing us to use a tree data structure.
 *
 * The actual representation of the tree is done with the [EncodedPartitions] type. The "root" of this tree is modeled
 * using the [WithModel] (private) class. There, the "labels" from the root to the child nodes are the keys in the map.
 * Further children are modelled with the [EncodedPartitions.ReferenceValue] class, see there for more details.
 *
 * This type [IndexedAbstractPointer] serves the same role as the [analysis.ip.InternalFuncValueLocation]
 * type; i.e., describing the partitions of memory needed to access any
 * field reachable from a "root" object. The [EncodedPartitions] class then serves a similar role to [analysis.ip.InternalFuncValueLocation.PointerLayoutInfo]
 * in the [analysis.ip.InternalFuncValueLocation] class.
 */
sealed interface IndexedAbstractPointer : AbstractTraversal<PartitionLike<*>, IndexedAbstractPointer> {
    /**
     * Return a pair of the [PartitionLike], which describes the memory map in which the data for [f] is stored,
     * and the [IndexedAbstractPointer] representing the abstract object layout of values stored in that location.
     *
     * If the value stored in [f] is not a reference type, then this second component will be a trivial object
     * which supports no deref operations.
     */
    override fun deref(f: PartitionField) : Pair<PartitionLike<*>, IndexedAbstractPointer>?

    /**
     * Return a "single-level" view of this abstract pointer: a map from the partition fields of the object to the
     * [PartitionLike] representation of the partitions which hold their values.
     */
    override fun toAbstractObject(): Map<PartitionField, PartitionLike<*>>

    companion object {
        /**
         * Used to describe any object that is known to not be an actual reference type, e.g., some scalar.
         *
         * This was chosen over a sum type for [IndexedAbstractPointer] as it significantly simplifies the implementation
         * ([deref] will only ever be called on a "real" pointer due to well-typing, and the nullability of the return type
         * is handled elsewhere in case we screw this up)
         */
        private data object TrivialPointer : IndexedAbstractPointer {
            override fun deref(f: PartitionField): Pair<PartitionLike<*>, IndexedAbstractPointer>? {
                return null
            }

            override fun toAbstractObject(): Map<PartitionField, PartitionLike<*>> {
                return mapOf()
            }
        }


        fun nullaryPointer() : IndexedAbstractPointer {
            return TrivialPointer
        }

        operator fun invoke(
            f: Map<PartitionField, EncodedPartitions>,
            transient: TransientCallId,
        ) : IndexedAbstractPointer {
            return WithModel(f, transient)
        }
    }

    /**
     * This class is expected to be used for values which are known to be reference types, i.e., those types
     * which have some coherent value for [abstractFields]. This class is used *before* inlining, before any concrete call ids are
     * assigned to inlinings. Thus, multiple instances of the same [UnindexedPartition] across different inlinings are disambiguated
     * with the [transientId].
     */
    private class WithModel(
        val abstractFields: Map<PartitionField, EncodedPartitions>,
        val transientId: TransientCallId,
    ) : IndexedAbstractPointer {
        override fun deref(f: PartitionField): Pair<PartitionLike<*>, IndexedAbstractPointer>? {
            /**
             * Get the [EncodedPartitions] that holds the value for [f], or return null.
             */
            val fieldPartition = abstractFields[f]  ?: return null

            /**
             * Tag the unindexed partition with the transient call id, during actual inlining this is materialized
             * into a "real" memory partition.
             */
            val abstractPartition = TransientPartition(
                callIdx = transientId,
                partitionId = fieldPartition.part.id
            )

            /**
             * If the [EncodedPartitions] is known to itself hold reference values, get the abstract
             * pointer for that value, or the trivial pointer.
             */
            val next = (fieldPartition as? EncodedPartitions.ReferenceValue)?.fields?.let { WithModel(it, transientId) } ?: nullaryPointer()
            return abstractPartition to next
        }

        override fun toAbstractObject(): Map<PartitionField, PartitionLike<*>> {
            return abstractFields.mapValues {
                TransientPartition(
                    callIdx = transientId,
                    partitionId = it.value.part.id
                )
            }
        }
    }
}

/**
 * A thin wrapper around a [transientCallId], extending it with the [pointerFor] method to turn "raw" abstract object layout
 * information into [IndexedAbstractPointer]'s in the appropriate call id.
 */
@JvmInline
value class AbstractMemorySpace(
    private val transientCallId: TransientCallId
) {
    fun pointerFor(f: Map<PartitionField, EncodedPartitions>) : IndexedAbstractPointer {
        return IndexedAbstractPointer(
            f = f,
            transient = transientCallId,
        )
    }
}
