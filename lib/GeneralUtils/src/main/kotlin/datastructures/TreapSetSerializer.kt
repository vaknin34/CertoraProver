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

import com.certora.collect.*
import datastructures.stdcollections.*
import kotlinx.serialization.KSerializer
import kotlinx.serialization.builtins.SetSerializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import utils.*
import java.util.*

class TreapSetSerializer<@Treapable E>(
    private val elemSerializer: KSerializer<E>
) : KSerializer<TreapSet<E>> {

    private val underlyingSerializer = SetSerializer(elemSerializer)

    override val descriptor: SerialDescriptor = underlyingSerializer.descriptor

    override fun serialize(encoder: Encoder, value: TreapSet<E>) {
        underlyingSerializer.serialize(encoder, value)
    }

    override fun deserialize(decoder: Decoder): TreapSet<E> =
        underlyingSerializer.deserialize(decoder).toTreapSet()
}
