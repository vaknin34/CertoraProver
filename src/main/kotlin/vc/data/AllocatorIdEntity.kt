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

package vc.data

import allocator.Allocator

/**
 * A [UniqueIdEntity] where the id attached to these objects is generated from an [Allocator.Id] sequence.
 */
interface AllocatorIdEntity<T> : UniqueIdEntity<T> where T : AllocatorIdEntity<T>, T : java.io.Serializable {
    /**
     * Simplified version of [UniqueIdEntity.mapId], implementers need only pass their current id and the [Allocator.Id]
     * that yielded that id, and [f] will return a (consistently remapped) id from that same sequence.
     */
    fun mapId(f: (Allocator.Id, Int) -> Int) : T
    override fun mapId(f: (Any, Int, () -> Int) -> Int): T {
        return mapId { sort: Allocator.Id, id: Int ->
            f(sort, id) { Allocator.getFreshId(sort) }
        }
    }
}
