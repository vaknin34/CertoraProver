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

@file:kotlinx.serialization.UseSerializers(BigIntegerSerializer::class)
package analysis.pta.abi

import com.certora.collect.*
import utils.*
import java.math.BigInteger

@KSerializable
@Treapable
sealed interface PartitionField : AmbiSerializable {
    @KSerializable
    data class ArrayElement(val elementSize: BigInteger) : PartitionField {
        constructor(elementSize: Int) : this(elementSize.toBigInteger())
    }

    @KSerializable
    data class StructField(val offset: BigInteger) : PartitionField {
        constructor(offset: Int) : this(offset.toBigInteger())
    }

    @KSerializable
    object ArrayLength : PartitionField {
        override fun hashCode(): Int = utils.hashObject(this)
        private fun readResolve(): Any = ArrayLength
    }
}
