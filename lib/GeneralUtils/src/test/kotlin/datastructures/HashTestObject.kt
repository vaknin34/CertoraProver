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

import kotlinx.serialization.Serializable

@Serializable
class HashTestObject(val value: Int, val code: Int = value.hashCode()) : java.io.Serializable, Comparable<HashTestObject> {
    private constructor() : this(0, 0)
    override fun hashCode() = code
    override fun equals(other: Any?) = other is HashTestObject && other.value == this.value
    override fun compareTo(other: HashTestObject): Int {
        val v = this.value
        val ov = other.value
        return when {
            v < ov -> -1
            v > ov -> 1
            else -> 0
        }
    }
}
