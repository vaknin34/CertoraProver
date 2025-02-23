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

package spec.cvlast.abi

import spec.cvlast.abi.DataLayout.SequenceElement.Elements
import spec.cvlast.abi.DataLayout.SequenceElement.PackedBytes1
import java.math.BigInteger

/**
 * Describes how a type is low-level encoded into a buffer. Note that this encoding describes
 * how the *entire* type is encoded, and does not address how a top-level, CVL array type
 * is encoded (see [spec.cvlast.CVLType.PureCVLType.CVLArrayType] for a discussion of this
 * difference). The type [T] is the type of "terminal" nodes, which are usually some representation
 * of primitive or "non-aggregate" types.
 */
sealed class DataLayout<out T> {


    /**
     * The terminal node in a [DataLayout].
     */
    data class Terminal<T>(val t: T) : DataLayout<T>() {
        companion object
    }

    /**
     * Indicates that the encoding of [next] is dynamic, and to decode an instance of [next] at some location L in
     * the buffer, the value at L should be interpreted as a relative offset as in the Solidity ABI specification
     * (https://docs.soliditylang.org/en/develop/abi-spec.html). The relative offset is computed w.r.t. the
     * nearest [OpenScope] instance encountered on the traversal of the [DataLayout] to this point, it is an error
     * if no such [OpenScope] instance exists.
     */
    data class DynamicPointer<T>(val next: DataLayout<T>) : DataLayout<T>() {
        init {
            check(next !is DynamicPointer)
        }
    }

    /**
     * A dynamic (that is, of statically unknown length) sequence of elements, the encoding of which
     * is given by [sequenceElements].
     */
    data class SequenceOf<T>(val sequenceElements: SequenceElement<DataLayout<T>>) : DataLayout<T>()

    /**
     * When decoding (or encoding) values into a buffer, indicates that any [DynamicPointer] instances encountered within
     * [next] that do not encounter an intervening [OpenScope] instance should be interpreted with respect to the current location L
     * within the buffer.
     */
    data class OpenScope<T>(val next: DataLayout<T>) : DataLayout<T>()

    /**
     * A static, heterogeneous tuple of elements given by [elements], where the string component of the tuple
     * is the name of the field in the tuple (NB: there is no representation for unnamed tuples, but this can be added if
     * needed). The size of the tuples is the size of the [elements] list.
     */
    data class TupleOf<T>(val elements: List<Pair<String, DataLayout<T>>>) : DataLayout<T>() {
        constructor(vararg elems: Pair<String, DataLayout<T>>) : this(elems.map { it })
    }

    data class LengthTaggedTuple<T>(val elems: DataLayout<T>) : DataLayout<T>()

    /**
     * A static, homogeneuos tuple of elements, whose layout is given by [elem]. The number of elements
     * is [num].
     */
    data class StaticRepeatedOf<T>(val elem: DataLayout<T>, val num: BigInteger) : DataLayout<T>()

    /**
     * Represents how elements are encoded in dynamic AND static arrays.
     * [PackedBytes1] indicates that the elements are tightly packes Bytes1. [Elements] indicates
     * that the elements are laid out by [Elements.dataLayout], which must be at least word sized.
     *
     * Note that an instance of [Elements] does *not* necessarily mean that the the sequence is of dynamic length, simply
     * that the elements of the sequence have the indicated layout. Thus, the element encoding of a [StaticRepeatedOf]
     * can be described with [Elements], as can [SequenceOf].
     *
     * In other words, as suggested by the [spec.cvlast.CVLType.PureCVLType.CVLArrayType.elementEncoding] value,
     * asking for an element encoding represented by [SequenceElement] from all array types (static and dynamic)
     * is well-defined; when a [spec.cvlast.CVLType.PureCVLType.StaticArray] returns an instance of [Elements],
     * it is simply indicating that the elements of the static array are laid out sequentially, "unpacked", laid
     * out according to [Elements.dataLayout].
     *
     * To make this distinction clearer, we could have made [StaticRepeatedOf] wrap a [SequenceElement] instance in the
     * same way [SequenceOf] does. However, we do not have a type for tightly packed, statically sized bytes array,
     * so instances of `StaticRepeatedOf(SequenceElement.PackedBytes1)` don't make sense. We could require the [StaticRepeatedOf.elem]
     * field to be a [SequenceElement.Elements], but this just introduces a wrapping class that doesn't *do* anything
     * except cluttering up accesses.
     */
    sealed class SequenceElement<out T> {
        data class PackedBytes1(val isString: Boolean) : SequenceElement<Nothing>()
        data class Elements<T>(val dataLayout: T) : SequenceElement<T>()
    }
}
