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

package cache

import java.io.ObjectOutputStream
import java.io.OutputStream
import java.io.Serializable

class SubListAdaptingObjectOutput(oStr: OutputStream) : ObjectOutputStream(oStr) {
    init {
        this.enableReplaceObject(true)
    }

    override fun replaceObject(obj: Any): Any {
        if (obj is Function<*>) {
            throw UnsupportedOperationException(
                "Failed to serialize $obj because Function<*> instances cannot be serialized"
            )
        }
        /*
        This is a fun one.

         We use List.sublist in some cases, which doesn't actually copy the list range, simply
         creates a sublist object view backed by the original list. On mutable lists, the "backing"
         list may be mutated through this sublist view object.

         Kotlin still exposes the sublist in immutable lists, in which case the sublist object is
         functionally just another list which happens to be implemented by sharing internally.

         Unfortunately, for whatever reason, the inner SubList class ised by ArrayList
         (the default List implementation) does NOT implement serializable,
         causing the whole serialization process to tank.

         So we just make clones of lists that are not serializable. This is technically unsafe if
         ever someone intentionally serialized a mutable list and somewhere else in the object graph
         relies on the mutable sublist view, but we will almost certainly never do that.
         */
        return if(obj is List<*> && obj !is Serializable) {
            obj.toList()
        } else {
            obj
        }
    }
}