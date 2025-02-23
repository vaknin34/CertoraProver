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
import kotlinx.serialization.builtins.MapSerializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder

@OptIn(kotlinx.serialization.ExperimentalSerializationApi::class)
class LinkedArrayHashMapSerializer<K, V>(
        private val keySerializer: KSerializer<K>,
        private val valueSerializer: KSerializer<V>
) : KSerializer<LinkedArrayHashMap<K, V>> {
    private val mapSerializer = MapSerializer(keySerializer, valueSerializer)
    override val descriptor: SerialDescriptor =
            SerialDescriptor("LinkedArrayHashMap", mapSerializer.descriptor)
    override fun serialize(encoder: Encoder, value: LinkedArrayHashMap<K, V>) {
        encoder.encodeSerializableValue(mapSerializer, value)
    }
    override fun deserialize(decoder: Decoder): LinkedArrayHashMap<K, V> {
        return LinkedArrayHashMap<K, V>(decoder.decodeSerializableValue(mapSerializer))
    }
}
