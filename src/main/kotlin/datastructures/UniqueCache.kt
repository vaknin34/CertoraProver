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

package datastructures

/**
 * Used to keep a single copy of elements of given type (according to their [equals] and [hashCode]).
 * It can be used a standard [Set] to view the elements in it, and to add to it, use the invoke operator.
 *
 * Isn't thread-safe.
 */
class UniqueCache<E>(private val cache: MutableMap<E, E> = mutableMapOf()) : Set<E> by cache.keys {
    operator fun invoke(t: E): E = cache.computeIfAbsent(t) { t }
}