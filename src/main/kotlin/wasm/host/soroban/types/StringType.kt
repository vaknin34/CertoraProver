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
    Soroban string objects are buffer objects that hold UTF-8-encoded text.
 */
@KSerializable
@Treapable
object StringType : BufferType() {
    override fun hashCode() = hashObject(this)
    
    override val tag = Val.Tag.StringObject
    override val sizes = TACKeyword.SOROBAN_STRING_SIZES.toVar()
    override val mappings = TACKeyword.SOROBAN_STRING_MAPPINGS.toVar()
}
