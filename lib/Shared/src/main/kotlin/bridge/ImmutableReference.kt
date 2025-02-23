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

@file:UseSerializers(utils.BigIntegerSerializer::class)

package bridge

import bridge.types.SolidityTypeInstance
import com.certora.collect.*
import kotlinx.serialization.Serializable
import kotlinx.serialization.UseSerializers
import utils.*
import java.math.BigInteger

/**
 * Immutable reference represents an immutable value, which the constructor will use to rewrite the code with.
 */
@Serializable
@Treapable
data class ImmutableReference(
    val offset: Int,
    val length: Int,
    val varname: String,
    val value: BigInteger? = null,
    val type: SolidityTypeInstance
) : SerializableWithAdapter {
    private class Adapter(c: ImmutableReference? = null) :
        SerializationAdapter<ImmutableReference>(serializer(), c)

    override fun writeReplace(): Any = Adapter(this)
}
