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

import kotlinx.serialization.*
import kotlinx.serialization.descriptors.*
import kotlinx.serialization.encoding.*
import kotlinx.serialization.modules.*
import kotlin.reflect.*

/**
 * Allows reflection-based polymorphism of any type that implements [HasKSerializable].  Add to the SerializersModule
 * used for serializing/deserializing.
 */
@OptIn(ExperimentalSerializationApi::class)
inline fun <reified Base : HasKSerializable> SerializersModuleBuilder.reflectivePolymorphic() {
    polymorphicDefaultSerializer(Base::class) { ReflectivePolymorphicSerializer<Base>(it::class.java) }
    polymorphicDefaultDeserializer(Base::class) { ReflectivePolymorphicSerializer(it!!) }
}

/**
 * A serializer that mostly just defers to the default serializer for [concreteType], but renames its `serialName`
 * using the JVM class name.  This allows us to instantate the same serializer later, when we need to deserialize the
 * object.
 */
@OptIn(ExperimentalSerializationApi::class)
@PublishedApi internal class ReflectivePolymorphicSerializer<Base : HasKSerializable>(
    concreteType: Class<*>
) : KSerializer<Base> {

    companion object {
        const val prefix = "ReflectivePolymorphicSerializer::"
        private fun typeToSerialName(type: Class<*>) = prefix + type.name
        private fun serialNameToType(name: String) = Class.forName(name.removePrefix(prefix))
    }

    constructor(serialName: String) : this(serialNameToType(serialName))

    val originalSerializer = serializer(concreteType)
    val renamedDescriptor = SerialDescriptor(typeToSerialName(concreteType), originalSerializer.descriptor)

    private fun substituteDescriptor(descriptor: SerialDescriptor) = when (descriptor) {
        originalSerializer.descriptor -> renamedDescriptor
        else -> descriptor
    }

    inner class SubstitutingEncoder(val inner: Encoder) : Encoder by inner {
        override fun beginCollection(descriptor: SerialDescriptor, collectionSize: Int) =
            inner.beginCollection(substituteDescriptor(descriptor), collectionSize)
        override fun beginStructure(descriptor: SerialDescriptor) =
            inner.beginStructure(substituteDescriptor(descriptor))
    }

    override val descriptor: SerialDescriptor = renamedDescriptor

    override fun serialize(encoder: Encoder, value: Base) =
        originalSerializer.serialize(SubstitutingEncoder(encoder), value)

    override fun deserialize(decoder: Decoder) =
        originalSerializer.deserialize(decoder).uncheckedAs<Base>()
}
