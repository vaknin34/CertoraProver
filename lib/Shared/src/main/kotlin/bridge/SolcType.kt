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

@file:UseSerializers(BigIntegerDecimalSerializer::class)

package bridge

import com.certora.collect.*
import evm.EVM_WORD_SIZE
import kotlinx.serialization.Serializable
import kotlinx.serialization.UseSerializers
import spec.cvlast.typedescriptors.*
import tac.StructField
import tac.TACStorageType
import utils.SerializableWithAdapter
import utils.SerializationAdapter
import java.math.BigInteger

@Serializable
@Treapable
data class StructMember(
    val slot: BigInteger,
    val label: String,
    val type: String,
    val offset: Int
)

// TODO: SolidtyStorageTypeDescription
@Serializable
@Treapable
data class SolcType(
    val label: String,
    val numberOfBytes: BigInteger,
    val members: List<StructMember>? = null,
    val key: String? = null,
    val value: String? = null,
    val base: String? = null,
    val encoding: String,
    val lowerBound: BigInteger? = null,
    val upperBound: BigInteger? = null
) : SerializableWithAdapter {
    private class Adapter(c: SolcType? = null) : SerializationAdapter<SolcType>(
        serializer(), c)

    override fun writeReplace(): Any = Adapter(this)

    fun toStorageType(lookup: Map<String, SolcType>, descriptor: VMTypeDescriptor?) : TACStorageType? {
        return when(encoding) {
            "inplace" -> {
                if(members != null) {
                    val fields = mutableMapOf<String, StructField>()
                    val struct = (descriptor as? VMStructDescriptor)
                    for(mem in members) {
                        if(mem.label in fields) {
                            return null
                        }
                        val fieldDesc = struct?.fieldTypes?.get(mem.label)
                        fields[mem.label] = StructField(
                            offset = mem.offset,
                            slot = mem.slot,
                            type = lookup[mem.type]?.toStorageType(lookup, fieldDesc) ?: return null
                        )
                    }
                    TACStorageType.Struct(fields, this.label)
                } else if(base != null) {
                    val staticDesc = descriptor as? VMStaticArrayType
                    val baseType = lookup[base] ?: return null
                    if(baseType.numberOfBytes < EVM_WORD_SIZE) {
                        return TACStorageType.StaticArray(
                            numElements = this.numberOfBytes/EVM_WORD_SIZE,
                            elementType = baseType.toStorageType(lookup, staticDesc?.elementType) ?: return null,
                            elementSizeInWords = BigInteger.ONE,
                            elementSizeInBytes = baseType.numberOfBytes,
                            logicalSize = staticDesc?.numElements
                        )
                    }

                    if(baseType.numberOfBytes.mod(EVM_WORD_SIZE) != BigInteger.ZERO) {
                        return null
                    }

                    TACStorageType.StaticArray(
                        numElements = this.numberOfBytes / baseType.numberOfBytes,
                        elementType = baseType.toStorageType(lookup, staticDesc?.elementType) ?: return null,
                        elementSizeInWords = baseType.numberOfBytes / EVM_WORD_SIZE,
                        elementSizeInBytes = baseType.numberOfBytes,
                        logicalSize = staticDesc?.numElements
                    )
                } else if(this.numberOfBytes > EVM_WORD_SIZE) {
                    return null
                } else {
                    TACStorageType.IntegralType(
                        typeLabel = // special caaaaaase
                        if ((this.label.startsWith("contract ") || this.label == "address payable") && this.numberOfBytes.toInt() == 20) {
                            "address"
                        } else if (this.label.startsWith("enum ")) {
                            "uint8"
                        } else {
                            this.label
                        },
                        numBytes = this.numberOfBytes,
                        descriptor = descriptor as? VMValueTypeDescriptor,
                        lowerBound = this.lowerBound,
                        upperBound = this.upperBound
                    )
                }
            }
            "dynamic_array" -> {
                val arrayDesc = descriptor as? VMDynamicArrayTypeDescriptor
                TACStorageType.Array(
                    elementType = lookup[this.base]?.toStorageType(lookup, arrayDesc?.elementType) ?: return null,
                    elementSizeInBytes = lookup[this.base]?.numberOfBytes ?: return null
                )
            }
            "mapping" -> {
                val mapType = descriptor as? VMMappingDescriptor
                TACStorageType.Mapping(
                    keyType = this.key?.let(lookup::get)?.toStorageType(lookup, mapType?.keyType) ?: return null,
                    valueType = this.value?.let(lookup::get)?.toStorageType(lookup, mapType?.valueType) ?: return null
                )
            }
            "bytes" -> TACStorageType.Bytes
            else -> null
        }
    }

}
