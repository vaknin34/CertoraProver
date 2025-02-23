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
import evm.EVM_WORD_SIZE
import utils.containsAny
import java.math.BigInteger

fun HeapType.toPTType() = when(this) {
    is HeapType.Array,
    HeapType.ByteArray,
    HeapType.EmptyArray,
    is HeapType.OffsetMap -> IPointsToSet.Type.REFERENCE
    HeapType.Int -> IPointsToSet.Type.INT
    is HeapType.TVar -> this.ty.ifResolved(
        intChoice = IPointsToSet.Type.INT,
        ptrChoice = IPointsToSet.Type.REFERENCE
    ) ?: IPointsToSet.Type.UNKNOWN
}

class ValuePointsToSet(override val nodes: List<PTANode>, private val rootType: HeapType, val anySummary: Boolean) : TypedPointsToSet {
    override fun mayAlias(v: IPointsToSet): Boolean {
        return nodes.containsAny(v.nodes)
    }

    override fun mustAlias(v: IPointsToSet): Boolean {
        return v is ValuePointsToSet && !v.anySummary && !this.anySummary && (this.nodes.singleOrNull() ?: return false) == v.nodes.singleOrNull()
    }

    override val type: IPointsToSet.Type
        get() = rootType.toPTType()

    override val typeDesc: TypedPointsToSet.SimpleTypeDescriptor?
        get() = when(rootType) {
            is HeapType.Array,
            HeapType.ByteArray,
            HeapType.EmptyArray -> TypedPointsToSet.SimpleTypeDescriptor.ReferenceType.Array
            HeapType.Int -> TypedPointsToSet.SimpleTypeDescriptor.INT
            is HeapType.OffsetMap -> TypedPointsToSet.SimpleTypeDescriptor.ReferenceType.Struct(
                (rootType.sz / EVM_WORD_SIZE).toInt()
            )
            is HeapType.TVar -> null
        }
}

class WritableSet(
    override val nodes: List<PTANode>,
    private val rootType: HeapType,
    private val updateType: WritablePointsToSet.UpdateType
) : WritablePointsToSet {
    override fun mayAlias(v: IPointsToSet): Boolean {
        return nodes.containsAny(v.nodes)
    }

    override fun mustAlias(v: IPointsToSet): Boolean {
        return updateType == WritablePointsToSet.UpdateType.STRONG && nodes.size == 1 && v is WritablePointsToSet && v.strongestUpdate() == WritablePointsToSet.UpdateType.STRONG &&
                v.nodes == this.nodes
    }

    override val type: IPointsToSet.Type
        get() = rootType.toPTType()

    override fun strongestUpdate(): WritablePointsToSet.UpdateType {
        return updateType
    }
}

class IndexableSet(
    override val nodes: List<PTANode>,
    override val type: IPointsToSet.Type,
    override val elementSize: BigInteger,
    override val index: IntValue,
    private val isStrongBase : Boolean
) : IndexedWritableSet {
    override fun mayAlias(v: IPointsToSet): Boolean {
        return this.nodes.containsAny(v.nodes)
    }

    init {
        check(!isStrongBase || nodes.size == 1)
    }

    override val strongBasePointer: Boolean
        get() = isStrongBase

    override fun mustAlias(v: IPointsToSet): Boolean {
        return v is IndexedWritableSet &&
                v.offsetUpdate() == WritablePointsToSet.UpdateType.STRONG &&
                this.offsetUpdate() == WritablePointsToSet.UpdateType.STRONG &&
                index.c == v.index.c &&
                nodes.size == 1 &&
                nodes.single() == v.nodes.single()
    }

    override fun offsetUpdate(): WritablePointsToSet.UpdateType {
        return if(isStrongBase && index.isConstant) {
            WritablePointsToSet.UpdateType.STRONG
        } else {
            WritablePointsToSet.UpdateType.WEAK
        }
    }
}

