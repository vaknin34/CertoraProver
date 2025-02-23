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

@file:kotlinx.serialization.UseSerializers(utils.BigIntegerSerializer::class)
package tac

import bridge.SolcType
import bridge.StorageSlot
import bridge.StorageTestOnly
import bridge.types.DescriptionAnnotation
import bridge.types.SolidityTypeDescription
import bridge.types.SolidityTypeInstance
import com.certora.collect.*
import evm.EVM_BYTE_SIZE
import evm.EVM_WORD_SIZE
import kotlinx.serialization.json.Json
import spec.CVLWarningLogger
import spec.cvlast.typedescriptors.VMTypeDescriptor
import spec.cvlast.typedescriptors.VMValueTypeDescriptor
import tac.TACStorageType.Bytes.toStorageType
import utils.CVLSerializerModules
import utils.SerializableWithAdapter
import utils.SerializationAdapter
import java.io.Serializable
import java.math.BigInteger

@kotlinx.serialization.Serializable
@Treapable
data class StructField(val type: TACStorageType, val slot: BigInteger, val offset: Int)

@kotlinx.serialization.Serializable
@Treapable
sealed class TACStorageType : SerializableWithAdapter {
    private class Adapter(ty: TACStorageType? = null) : SerializationAdapter<TACStorageType>(serializer(), ty) {
        override val json: Json = Json {
            serializersModule = CVLSerializerModules.modules
        }
    }
    override fun writeReplace(): Any {
        return Adapter(this)
    }

    @kotlinx.serialization.Serializable
    data class Mapping(val keyType: TACStorageType, val valueType: TACStorageType) : TACStorageType() {
        override fun toErrorString(): String {
            return "mapping (${keyType.toErrorString()} => ${valueType.toErrorString()})"
        }
    }
    @kotlinx.serialization.Serializable
    object Bytes : TACStorageType() {
        override fun hashCode() = utils.hashObject(this)
        fun readResolve(): Any = Bytes

        override fun toErrorString(): String {
            return toString()
        }
    }
    @kotlinx.serialization.Serializable
    data class Struct(val members: Map<String, StructField>, val label: String) : TACStorageType() {
        override fun toErrorString(): String {
            return label
        }
    }
    @kotlinx.serialization.Serializable
    data class IntegralType(val typeLabel: String, val numBytes: BigInteger, val descriptor: VMValueTypeDescriptor?, val lowerBound: BigInteger?, val upperBound: BigInteger?) : TACStorageType() {
        override fun toErrorString(): String {
            return typeLabel
        }
        val numBits get() = (numBytes * EVM_BYTE_SIZE).intValueExact()
    }
    @kotlinx.serialization.Serializable
    data class StaticArray(
        val numElements: BigInteger,
        val elementType: TACStorageType,
        val elementSizeInWords: BigInteger,
        val elementSizeInBytes: BigInteger,
        val logicalSize: BigInteger?
    ) : TACStorageType() {
        override fun toErrorString(): String {
            return "${this.elementType.toErrorString()}[$numElements]"
        }
    }
    @kotlinx.serialization.Serializable
    data class Array(val elementType: TACStorageType, val elementSizeInBytes: BigInteger) : TACStorageType() {
        override fun toErrorString(): String {
            return "${elementType.toErrorString()}[]"
        }
    }

    abstract fun toErrorString() : String

    fun toStorageType(typeDescriptor: SolidityTypeDescription): TACStorageType? = runCatching {
        val annotation = typeDescriptor.annotations.filterIsInstance<DescriptionAnnotation.StorageAnnotation>().single()

        when (typeDescriptor) {
            is SolidityTypeDescription.Function -> {
                error("Type Function is currently not supported")
            }

            is SolidityTypeDescription.UserDefined.Enum -> {
                IntegralType(
                    typeLabel = typeDescriptor.toString(),
                    numBytes = annotation.numberOfBytes,
                    lowerBound = annotation.lowerBound,
                    upperBound = annotation.upperBound,
                    descriptor = typeDescriptor.toVMTypeDescriptor(null) as? VMValueTypeDescriptor
                )
            }

            is SolidityTypeDescription.UserDefined.ValueType -> {
                IntegralType(
                    typeLabel = typeDescriptor.valueTypeAliasedName.toString(),
                    numBytes = annotation.numberOfBytes,
                    lowerBound = annotation.lowerBound,
                    upperBound = annotation.upperBound,
                    descriptor = typeDescriptor.toVMTypeDescriptor(null) as? VMValueTypeDescriptor
                )

            }

            is SolidityTypeDescription.Primitive -> {
                IntegralType(
                    typeLabel = typeDescriptor.primitiveName.toString(),
                    numBytes = annotation.numberOfBytes,
                    lowerBound = annotation.lowerBound,
                    upperBound = annotation.upperBound,
                    descriptor = typeDescriptor.toDescriptor()
                )
            }

            is SolidityTypeDescription.Contract -> {
                IntegralType(
                    typeLabel = typeDescriptor.toString(),
                    numBytes = annotation.numberOfBytes,
                    lowerBound = annotation.lowerBound,
                    upperBound = annotation.upperBound,
                    descriptor = typeDescriptor.toVMTypeDescriptor(null) as? VMValueTypeDescriptor
                )
            }

            is SolidityTypeDescription.UserDefined.Struct -> {

                val fields = typeDescriptor.structMembers.associate { member ->

                    val memberAnnotation =
                        member.type.annotations.filterIsInstance<DescriptionAnnotation.StorageAnnotation>().single()
                    member.name to StructField(
                        offset = memberAnnotation.offset ?: error("didn't find struct member offset"),
                        slot = memberAnnotation.slot ?: error("didn't find struct member slot"),
                        type = toStorageType(member.type)
                            ?: error("could not convert struct member: $member to TACStorageType")
                    )
                }

                Struct(fields, typeDescriptor.structName)
            }

            is SolidityTypeDescription.StaticArray -> {

                val baseType = typeDescriptor.staticArrayBaseType
                val baseTypeAnnotation =
                    baseType.annotations.filterIsInstance<DescriptionAnnotation.StorageAnnotation>().single()

                val baseSize = baseTypeAnnotation.numberOfBytes
                val arraySize = annotation.numberOfBytes

                when {
                    baseSize <= EVM_WORD_SIZE -> StaticArray(
                        numElements = arraySize / EVM_WORD_SIZE,  //num slots in the array
                        elementType = toStorageType(baseType)
                            ?: error("cannot convert elementType of static array: $baseType"),
                        elementSizeInWords = BigInteger.ONE,
                        elementSizeInBytes = baseSize,
                        logicalSize = typeDescriptor.staticArraySize
                    )


                    else -> {
                        if (baseSize.mod(EVM_WORD_SIZE) != BigInteger.ZERO) {
                            error(
                                "array base type that is not elementary is padded and should be aligned to EVM WORD SIZE: $EVM_WORD_SIZE, but this one is not: $baseSize"
                            )
                        }
                        StaticArray(
                            numElements = arraySize / baseSize, //num elements
                            elementType = toStorageType(baseType)
                                ?: error("cannot convert elementType of static array: $baseType"),
                            elementSizeInWords = baseSize / EVM_WORD_SIZE, //num of slots per element
                            elementSizeInBytes = baseSize,
                            logicalSize = typeDescriptor.staticArraySize
                        )
                    }

                }
            }


            is SolidityTypeDescription.Array -> {
                Array(
                    elementType = toStorageType(typeDescriptor.dynamicArrayBaseType)
                        ?: error("cannot convert elementType of dynamic array: $typeDescriptor.dynamicArrayBaseType"),
                    elementSizeInBytes = typeDescriptor.dynamicArrayBaseType.annotations.filterIsInstance<DescriptionAnnotation.StorageAnnotation>().single().numberOfBytes
                )
            }

            is SolidityTypeDescription.Mapping -> {
                Mapping(
                    keyType = toStorageType(typeDescriptor.mappingKeyType)
                        ?: error("cannot convert keyType: $typeDescriptor.mappingKeyType"),
                    valueType = toStorageType(typeDescriptor.mappingValueType)
                        ?: error("cannot convert valueType: $typeDescriptor.mappingValueType")
                )
            }

            is SolidityTypeDescription.StringType, is SolidityTypeDescription.PackedBytes -> Bytes
        }
    }.onFailure { e ->
        CVLWarningLogger.generalWarning(
            e.toString()
        )
    }.getOrNull()
}

@Treapable
data class TACStorageSlot(
    val label: String, val slot: BigInteger, val offset: Int,
    val storageType: TACStorageType?,
    val typeDescriptor: VMTypeDescriptor?
) : Serializable {
    val offsetInBytes : Int
        get() = offset

    constructor(slot: StorageSlot, types: Map<String, SolcType>?) :
        this(slot.label, slot.slot, slot.offset, slotType(slot, types), slot.descriptor?.let { SolidityTypeInstance(it, null) }?.toVMTypeDescriptor())

    companion object {
        @OptIn(StorageTestOnly::class)
        private fun slotType(slot: StorageSlot, types: Map<String, SolcType>?): TACStorageType? {
            return slot.descriptor?.let { toStorageType(it) }
                ?: types?.let { typesNotNull ->
                    typesNotNull[slot.type]?.toStorageType(typesNotNull, null)
                }
        }
    }

}

@Treapable
data class TACStorageLayout(val storageHashArgsReversed: Boolean, val slots: Map<String, TACStorageSlot>) : Serializable, Map<String, TACStorageSlot> by slots
