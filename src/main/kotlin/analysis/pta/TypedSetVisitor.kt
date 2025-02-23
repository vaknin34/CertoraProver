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
import analysis.pta.TypedSetVisitor.VisitError
import evm.EVM_WORD_SIZE
import java.math.BigInteger

typealias VisitResult = TypedSetVisitor.VisitError?

/**
 * Aids in traversing a [TypedPointsToSet] "structurally".
 * Each callback below can return a [VisitError], which will halt the visiting process.
 */
interface TypedSetVisitor {
    /**
     * Called when a [TypedPointsToSet] has an array element field, represented by [s].
     */
    fun arrayField(s: IndexedWritableSet) : VisitResult

    /**
     * Called when a [TypedPointsToSet] has a length field, represented by [s].
     */
    fun arrayLengthField(s: IPointsToSet) : VisitResult

    /**
     * Called when a [TypedPointsToSet] has a "struct" field represented by [s] at offset [o].
     */
    fun structField(o: BigInteger, s: WritablePointsToSet) : VisitResult

    /**
     * Called when the points to set is actually a primitive value.
     */
    fun primitive()

    enum class VisitError {
        NO_LENGTH_FIELD_FOR_ARRAY,
        ARRAY_FIELD_NOT_INDEXED,
        NO_TYPE_INFO,
        MISSING_FIELD_FOR_STRUCT,
        CALLBACK_ERROR
    }

    companion object {
        val OK : VisitResult = null

        /**
         * Using [visitor], visit the fields that should available on [this] according to its [analysis.pta.TypedPointsToSet.SimpleTypeDescriptor].
         * [pta] is used for generating the field sets, and heap contents and fields are interpreted according to the program
         * state at [where].
         *
         * Returns a [VisitError] if the visiting process failed, or null if no such error occurred.
         */
        fun TypedPointsToSet.accept(where: CmdPointer, pta: IPointsToInformation, visitor: TypedSetVisitor) : VisitError? {
            when(val td = this.typeDesc) {
                TypedPointsToSet.SimpleTypeDescriptor.INT -> visitor.primitive()
                TypedPointsToSet.SimpleTypeDescriptor.ReferenceType.Array -> {
                    val retPta = this
                    val len = pta.lengthFieldAt(where, retPta) ?: return VisitError.NO_LENGTH_FIELD_FOR_ARRAY
                    visitor.arrayLengthField(len)?.let {
                        return it
                    }

                    pta.arrayFieldAt(where, retPta)?.let { elemFields ->
                        if(elemFields !is IndexedWritableSet) {
                            return VisitError.ARRAY_FIELD_NOT_INDEXED
                        }
                        visitor.arrayField(elemFields)?.let {
                            return it
                        }
                    }
                }
                is TypedPointsToSet.SimpleTypeDescriptor.ReferenceType.Struct -> {
                    for(fieldInd in 0 until td.nFields) {
                        val fieldOffset = fieldInd.toBigInteger() * EVM_WORD_SIZE
                        val fld = pta.fieldNodesAt(where, this, fieldOffset) ?: return VisitError.MISSING_FIELD_FOR_STRUCT
                        visitor.structField(fieldOffset, fld)?.let {
                            return it
                        }
                    }
                }
                null -> return VisitError.NO_TYPE_INFO
            }
            return null
        }
    }
}
