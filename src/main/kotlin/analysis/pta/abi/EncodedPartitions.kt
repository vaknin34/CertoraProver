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

import datastructures.stdcollections.*
import com.certora.collect.*
import utils.AmbiSerializable
import utils.KSerializable
import vc.data.UniqueIdEntity

/**
 * Part of the representation of an abstract object layout. In the terminology of used in the
 * documentation of [analysis.icfg.IndexedAbstractPointer], these are the non-root "nodes" in the tree
 * that describes where the data of an object resides. [part] indicates the partition of the field itself.
 * If the field is itself a reference type (and thus, has labeled children) then [ReferenceValue] is
 * used, with the children labeled using the keys in the [ReferenceValue.fields] map (which serves
 * the same role as [analysis.icfg.IndexedAbstractPointer.WithModel.abstractFields]. In other words, [EncodedPartitions]
 * always appears as the codomain of a map whose keys are [PartitionField].
 *
 * The layout information encoded in this class does *not* include call index information, that is provided by
 * the enclosing [analysis.icfg.IndexedAbstractPointer] class, or if before inlining, it assumed to be the root index 0.
 */
@KSerializable
@Treapable
sealed interface EncodedPartitions : UniqueIdEntity<EncodedPartitions>, AmbiSerializable {
    val part: UnindexedPartition

    /**
     * A partition ([part]) which holds a scalar (or primitive) value. As this value lives in memory,
     * this partition is (assumed) to "correspond" to some abstract field in an object, but that is not
     *  recorded as part of this class (rather, that information is implicitly given by the
     *  [PartitionField] key under which this object was stored in some map (see above).
     */
    @KSerializable
    data class ScalarValue(override val part: UnindexedPartition) : EncodedPartitions {
        override fun mapId(f: (Any, Int, () -> Int) -> Int): EncodedPartitions {
            return ScalarValue(part.mapId(f))
        }
    }

    /**
     * A representation of a partition that holds reference values, and that reference value's abstract object layout.
     * Like [ScalarValue] above, this partition corresponds to some abstract field in another object, which is given
     * by how this class is "reached".
     *
     * Note that [fields] does **not** give the field information about the object that *includes* this field. Rather,
     * [fields] gives information about the abstract layout of the fields of the reference value stored in [part] (which,
     * again, itself is a field of some other object).
     */
    @KSerializable
    data class ReferenceValue(
        override val part: UnindexedPartition,
        val fields: Map<PartitionField, EncodedPartitions>
    ) : EncodedPartitions {
        override fun mapId(f: (Any, Int, () -> Int) -> Int): EncodedPartitions {
            return ReferenceValue(
                fields = this.fields.mapValues { (_, pv) ->
                    pv.mapId(f)
                },
                part = part.mapId(f)
            )
        }
    }
}
