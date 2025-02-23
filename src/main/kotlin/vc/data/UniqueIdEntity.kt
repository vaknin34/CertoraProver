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

/**
 * Indicates that this is an "entity" (a summary or an annotation) that
 * has a unique id, and which supports generating "consistent" fresh ids via [mapId].
 *
 * This consistent (re)generation is done within some batch, i.e., it is expected
 * that if one entity with an id is remapped, then all such entities are likewise remapped.
 */
interface UniqueIdEntity<T> : java.io.Serializable where T : UniqueIdEntity<T>, T : java.io.Serializable {

    /**
     * Map this entities unique ID using [f]. [f] makes the following promise:
     *
     * For any possible x, i, g, if f(x, i, g) was already called and returned L, then f(x, i, g') will return
     * L from f(x, i, g') for any g', _without invoking g'_ (as g' is allowed to have side-effects).
     * Otherwise, [f] calls the third parameter to generate a new id to associated with x, i, such
     * that any call to f(x, i, g'') will return the result of invoking g.
     *
     * It is expected that when remapping multiple such entities within a "batch", the same [f] is
     * passed to all entities.
     *
     * In practice, it is expected that implementers of this interface derive their unique id from
     * some unique, monotonically increasing sequence (e.g.,
     * the numbers associated with an [allocator.Allocator.Id]). When that implementers [mapId]
     * is called, it will call [f] with the identifier of the sequence, the current id, and a "new id generator"
     * (e.g., a function that generates the next value in the [allocator.Allocator.Id] sequence). Thus, all
     * entities with the same id from the same sequence will be *consistently* remapped to a fresh id without coordination.
     */
    fun mapId(f: (Any, Int, () -> Int) -> Int) : T
}
