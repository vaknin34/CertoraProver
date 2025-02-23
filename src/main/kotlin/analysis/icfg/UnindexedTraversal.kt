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

import datastructures.stdcollections.*
import analysis.pta.abi.EncodedPartitions
import analysis.pta.abi.PartitionField
import analysis.pta.abi.UnindexedPartition

/** An abstract traversal where the underlying partitions' call indices are unknown (see [IndexedAbstractPointer]).
 *
 *  In practice, we use an [UnindexedTraversal] in a way that is analogous to the formal arguments of a function
 *  when (in our case) performing inlining: we check that the caller's [IndexedAbstractPointer] matches the shape
 *  of the [UnindexedTraversal], and then substitute the indexed caller partitions for the corresponding
 *  callee [UnindexedTraversal].
 */
data class UnindexedTraversal(val fields: Map<PartitionField, EncodedPartitions>) : AbstractTraversal<UnindexedPartition, UnindexedTraversal> {
    override fun deref(f: PartitionField): Pair<UnindexedPartition, UnindexedTraversal>? {
        return fields[f]?.let { e ->
            val p = e.part
            p to when(e) {
                is EncodedPartitions.ReferenceValue -> UnindexedTraversal(e.fields)
                is EncodedPartitions.ScalarValue -> UnindexedTraversal(mapOf())
            }
        }
    }

    override fun toAbstractObject(): Map<PartitionField, UnindexedPartition> {
        return fields.mapValues {
            it.value.part
        }
    }
}
