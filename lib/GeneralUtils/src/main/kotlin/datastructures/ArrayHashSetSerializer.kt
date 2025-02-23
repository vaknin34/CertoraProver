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

import kotlinx.serialization.KSerializer
import kotlinx.serialization.builtins.SetSerializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

@OptIn(kotlinx.serialization.ExperimentalSerializationApi::class)
class ArrayHashSetSerializer<E>(private val elementSerializer: KSerializer<E>) :
        KSerializer<ArrayHashSet<E>> {
    private val setSerializer = SetSerializer(elementSerializer)
    override val descriptor: SerialDescriptor =
            SerialDescriptor("ArrayHashSet", setSerializer.descriptor)
    override fun serialize(encoder: Encoder, value: ArrayHashSet<E>) {
        encoder.encodeSerializableValue(setSerializer, value)
    }
    override fun deserialize(decoder: Decoder): ArrayHashSet<E> {
        return ArrayHashSet<E>(decoder.decodeSerializableValue(setSerializer))
    }
}

