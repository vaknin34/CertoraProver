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

@file:UseSerializers(BigIntegerSerializer::class)
package tac

import com.certora.collect.*
import datastructures.stdcollections.*
import kotlinx.serialization.UseSerializers
import utils.*
import java.math.BigInteger

/**
 * Describes in very coarse grained terms how values are laid out within arrays.
 * The [toFields] describes what traversals (if any), represented with [DataField],
 * are possible on values with this type, and what [ObjectShape] is yielded after
 * taking that step.
 */
@KSerializable
@Treapable
sealed interface ObjectShape : AmbiSerializable {
    fun toFields(): Map<DataField, ObjectShape>

    /**
     * The value is a primitive value, encoded with [enc]
     */
    @KSerializable
    data class Primitive(val enc: Tag.CVLArray.UserArray.ElementEncoding) : ObjectShape {
        override fun hashCode(): kotlin.Int {
            return hash { it + enc }
        }

        override fun toFields(): Map<DataField, ObjectShape> {
            return mapOf()
        }
    }

    /**
     * The value is an array whose elements are described (recursively) with [elements].
     * The array is packed with [isPacked]
     */
    @KSerializable
    @Treapable
    data class Array(val elements: ObjectShape, val isPacked: Boolean) : ObjectShape {
        /**
         * Two possible traversals, getting the length of this array, or getting its data.
         */
        override fun toFields(): Map<DataField, ObjectShape> {
            return mapOf(
                DataField.ArrayData to elements,
                DataField.ArrayLength to Primitive(Tag.CVLArray.UserArray.ElementEncoding.Unsigned)
            )
        }
    }

    /**
     * A struct with named fields with their own object shape. The ordering in this list
     * is significant: the first field is access at the pointer to the struct with this shape,
     * the second such field is accessed at the pointer to this struct + 32, the third field
     * is accessed at the pointer to this struct + 64, etc.
     */
    @KSerializable
    @Treapable
    data class Struct(val fields: List<Pair<String, ObjectShape>>) : ObjectShape {
        /**
         * One traversal per field
         */
        override fun toFields(): Map<DataField, ObjectShape> {
            return fields.associate { (fldName, fldShape) ->
                DataField.StructField(fldName) to fldShape
            }
        }
    }

    /**
     * A static struct with [length] and whose elements have shape [elements].
     */
    @KSerializable
    @Treapable
    data class StaticArray(val elements: ObjectShape, val length: BigInteger) : ObjectShape {
        /**
         * As [Array] above, without the length field
         */
        override fun toFields(): Map<DataField, ObjectShape> {
            return mapOf(
                DataField.ArrayData to elements
            )
        }
    }
}
