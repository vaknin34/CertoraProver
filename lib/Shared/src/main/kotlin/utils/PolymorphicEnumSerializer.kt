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

@file:OptIn(kotlinx.serialization.ExperimentalSerializationApi::class)

package utils

import kotlinx.serialization.KSerializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.encoding.CompositeDecoder.Companion.DECODE_DONE
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.encoding.decodeStructure
import kotlinx.serialization.encoding.encodeStructure

/**
 * A serializer which supports registering [Enum]s as subclasses in polymorphic serialization when class discriminators are used.
 * When class discriminators are used, an enum is not encoded as a structure which the class discriminator can be added to.
 * An exception is thrown when initializing Json: "Serializer for <enum> of kind ENUM cannot be serialized polymorphically with class discriminator."
 * This serializer encodes the enum as a structure with a single `value` holding the enum value.
 *
 * Use this serializer to register the enum in the serializers module, e.g.:
 * `subclass( <enum>::class, PolymorphicEnumSerializer( <enum>.serializer() )`
 *
 * This is an adaptation of
 * https://github.com/cph-cachet/carp.core-kotlin/blob/7d227515d8698ba893862092a83e29b9645df7eb/
 *  carp.common/src/commonMain/kotlin/dk/cachet/carp/common/infrastructure/serialization/PolymorphicEnumSerializer.kt
 */
class PolymorphicEnumSerializer<T : Enum<T>>(private val enumSerializer: KSerializer<T>) : KSerializer<T> {
    override val descriptor: SerialDescriptor = buildClassSerialDescriptor(enumSerializer.descriptor.serialName) {
        element("value", enumSerializer.descriptor)
    }

    override fun deserialize(decoder: Decoder): T =
        decoder.decodeStructure(descriptor) {
            when (val valueFieldIndex = decodeElementIndex(descriptor)) {
                0 -> {
                    val nextElemIndex = decodeElementIndex(descriptor)
                    if (nextElemIndex != DECODE_DONE) {
                        throw IllegalStateException(
                            "Expected $valueFieldIndex to be the index of the last serialized field," +
                                    "but found that it has a successor ($nextElemIndex)"
                        )
                    }
                    decodeSerializableElement(descriptor, valueFieldIndex, enumSerializer)
                }
                else -> {
                    throw IllegalStateException("Expected to get an element index of 0, but got $valueFieldIndex")
                }
            }
        }

    override fun serialize(encoder: Encoder, value: T) =
        encoder.encodeStructure(descriptor) {
            encodeSerializableElement(descriptor, 0, enumSerializer, value)
        }
}