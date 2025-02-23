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

package spec.cvlast.abi

import tac.Tag

/**
 * A marker interfaces for types that have a primitive buffer representation, i.e., can be encoded in a single word
 * within a buffer, the encoding of which is described by [bufferEncoding]
 */
interface PrimitiveBufferRepresentation {
    val bufferEncoding: Tag.CVLArray.UserArray.ElementEncoding
}
