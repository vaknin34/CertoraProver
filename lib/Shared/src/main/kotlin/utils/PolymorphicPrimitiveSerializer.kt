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

package utils

import kotlinx.serialization.KSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import kotlinx.serialization.encoding.decodeStructure
import kotlinx.serialization.encoding.encodeStructure
import java.math.BigInteger

/**
 * This class allows us to serialize polymorphically any primitive type. it simply wraps up the primitive type and allows
 * to include this as Any in a polymorphic serialization.
 */
@OptIn(kotlinx.serialization.ExperimentalSerializationApi::class)
class PolymorphicPrimitiveSerializer<T> (private val typeSerializer: KSerializer<T>) : KSerializer<T>
{
    override val descriptor: SerialDescriptor = buildClassSerialDescriptor( typeSerializer.descriptor.serialName )
    {
        element( "value", typeSerializer.descriptor )
    }
    override fun deserialize( decoder: Decoder): T =
        decoder.decodeStructure( descriptor ) {
            decodeElementIndex( descriptor )
            decodeSerializableElement( descriptor, 0,typeSerializer)
        }

    override fun serialize(encoder: Encoder, value: T) {
        encoder.encodeStructure( descriptor ) {
            encodeSerializableElement( descriptor, 0, typeSerializer, value )
        }
    }
}


/** BigIntegerSerializerPolymorphic:
 * it wraps the String primitive,
 * and save the type of BigInteger that needs to be when deserializing polymorphic objects \
 *  */
object BigIntegerSerializerPolymorphic :
    KSerializer<BigInteger> {
    const val radix = 16
    override val descriptor: SerialDescriptor = buildClassSerialDescriptor( "BigInteger" )
    {
        element( "value", String.serializer().descriptor )
    }
    override fun deserialize( decoder: Decoder): BigInteger =


        decoder.decodeStructure( descriptor ) {
            decodeElementIndex( descriptor )
            BigInteger(decodeSerializableElement( descriptor, 0, String.serializer()), radix)
        }

    override fun serialize(encoder: Encoder, value: BigInteger) {
        encoder.encodeStructure( descriptor ) {
            encodeSerializableElement( descriptor, 0, String.serializer(), value.toString(radix) )
        }
    }

}
