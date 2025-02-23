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

package wasm.host.soroban.types

import com.certora.collect.*
import utils.*
import vc.data.*
import wasm.host.soroban.*

/**
    Soroban bytes objects are buffer objects that hold arbitrary binary data of any length.
 */
@KSerializable
@Treapable
object BytesType : BufferType() {
    override fun hashCode() = hashObject(this)
    
    override val tag = Val.Tag.BytesObject
    override val sizes = TACKeyword.SOROBAN_BYTES_SIZES.toVar()
    override val mappings = TACKeyword.SOROBAN_BYTES_MAPPINGS.toVar()
}
