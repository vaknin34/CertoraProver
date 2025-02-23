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

import analysis.numeric.IntValue
import datastructures.stdcollections.*
import utils.*
import java.math.BigInteger

interface IPointsToSet {
    /**
     * May this points to set alias with another points to set?
     */
    fun mayAlias(v: IPointsToSet) : Boolean

    /**
     * MUST this points to set alias with another points to set?
     */
    fun mustAlias(v: IPointsToSet) : Boolean

    /**
     * The set of opaque-ish points to nodes that represent some abstraction of the runtime heap. It is expected that
     * each concrete memory block be abstracted to a (unique) abstract PTANode.
     */
    val nodes: Collection<PTANode>


    /**
     * The types of objects abstracted by this points to set.
     */
    enum class Type {
        REFERENCE,
        INT,
        UNKNOWN,
        COMPILER, // do not look at the value of this pointer, the compiler sets it (only used for length fields)
        NOTHING;
    }

    val type : Type

    class None : IPointsToSet {
        override fun mayAlias(v: IPointsToSet): Boolean = true
        override fun mustAlias(v: IPointsToSet): Boolean = false
        override val nodes: Collection<PTANode> = listOf(PTANode.None())
        override val type: Type = Type.UNKNOWN
        override fun hashCode() = hash { it + nodes + type }
    }
}

interface TypedPointsToSet : IPointsToSet {
    sealed class SimpleTypeDescriptor {
        object INT : SimpleTypeDescriptor()
        sealed class ReferenceType : SimpleTypeDescriptor() {
            object Array : ReferenceType()
            data class Struct(val nFields: Int) : ReferenceType()
        }
    }

    val typeDesc: SimpleTypeDescriptor?
}

interface WritablePointsToSet : IPointsToSet {

    /**
     * What are the types of updates supported by a points-to set?
     */
    enum class UpdateType {
        /**
         * You can strongly update the contents pointed to by the pointer, there is no ambiguity about where it points
         */
        STRONG,

        /**
         * Only weak updates are admitted. The nodes returned by this set may or may not support offset tracking.
         */
        WEAK,

        /**
         * The contents of this pointer should not be written
         */
        INVALID
    }

    /**
     * What is the strongest type of update supported through pointers with this
     * points to set?
     * @see [UpdateType]
     */
    fun strongestUpdate() : UpdateType
}

interface IndexedWritableSet : WritablePointsToSet {
    val index: IntValue
    val elementSize: BigInteger
    override fun strongestUpdate(): WritablePointsToSet.UpdateType = WritablePointsToSet.UpdateType.WEAK
    fun offsetUpdate(): WritablePointsToSet.UpdateType
    val strongBasePointer: Boolean

    data class IndexedNode(val node: PTANode, val index: IntValue, val elementSize: BigInteger)

    val indexed get() = this.nodes.map {
        IndexedNode(
            it, index, elementSize
        )
    }
}

