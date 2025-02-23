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

package tac

import com.certora.collect.*
import utils.AmbiSerializable
import utils.KSerializable
import utils.hashObject

/**
 * Corresponds to a single "step" of a traversal
 * through an [ObjectShape].
 */
@KSerializable
@Treapable
sealed interface DataField : AmbiSerializable {
    /**
     * Corresponds to reading an array's data.
     */
    @KSerializable
    object ArrayData : DataField {
        fun readResolve(): Any {
            return ArrayData
        }
        override fun hashCode(): Int {
            return hashObject(this)
        }

        override fun toString() = "ArrayData"
    }

    /**
     * Corresponds to reading an array's length
     */
    @KSerializable
    object ArrayLength : DataField {
        fun readResolve(): Any {
            return ArrayLength
        }
        override fun hashCode(): Int {
            return hashObject(this)
        }

        override fun toString() = "ArrayLength"
    }

    /**
     * Corresponds to reading a struct's field [field]
     */
    @KSerializable
    data class StructField(val field: String) : DataField
}
