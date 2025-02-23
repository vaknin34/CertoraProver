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

package cache.utils

import allocator.Allocator
import vc.data.CoreTACProgram
import java.io.Serializable

data class TACWithAllocator(
    val tac: CoreTACProgram,
    val memento: Allocator.Memento
): Serializable {
    fun writeObject(filename: String) {
        ObjectSerialization.writeObject(this, filename)
    }

    companion object {
        fun readObject(filename: String): TACWithAllocator {
            return ObjectSerialization.readObject<TACWithAllocator>(filename)
        }
    }
}