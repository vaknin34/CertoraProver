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

import allocator.Allocator
import allocator.GenerateRemapper
import allocator.GeneratedBy
import tac.CallId
import utils.*
import vc.data.RemapperEntity

@KSerializable
@GenerateRemapper
data class UnindexedPartition(
    @GeneratedBy(Allocator.Id.MEMORY_PARTITION)
    val id: Int,
) : RemapperEntity<UnindexedPartition> {
    companion object {
        fun new() = UnindexedPartition(Allocator.getFreshId(Allocator.Id.MEMORY_PARTITION))
    }

    fun indexed(callIdx: CallId) = Partition(id, callIdx)
}
