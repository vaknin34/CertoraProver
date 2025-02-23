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

package compiler.data

import kotlinx.serialization.KSerializer
import kotlinx.serialization.Required
import kotlinx.serialization.Serializable
import kotlinx.serialization.SerializationException
import kotlinx.serialization.builtins.ListSerializer
import kotlinx.serialization.builtins.serializer
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.descriptors.buildClassSerialDescriptor
import kotlinx.serialization.encoding.CompositeDecoder
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import java.io.File

typealias FileSelector = String
typealias ContractSelector = String
typealias SolidityOutput = String

const val ALL_FILES : FileSelector = "*"
const val ALL_CONTRACTS : ContractSelector = "*"
const val WHOLE_FILE_SELECTOR : ContractSelector = ""

@Serializable
data class Input(
    @Required
    val language: String = "Solidity",
    val sources: Map<String, ContractSource>,
    val settings : SolcSettings
)

@Serializable
data class SolcSettings(
    val outputSelection: Map<FileSelector, Map<ContractSelector, List<SolidityOutput>>>,
    val optimizer: SolidityOptimization = SolidityOptimization(enabled = false)
)

@Serializable
data class SolidityOptimization(val enabled: Boolean)

object FileSourceSerializer : KSerializer<File> {
    private val listStringSerializer = ListSerializer(String.serializer())

    override val descriptor: SerialDescriptor
        get() = listStringSerializer.descriptor

    override fun deserialize(decoder: Decoder): File {
        val x = listStringSerializer.deserialize(decoder)
        assert(x.size == 1)
        val path = x.first()
        return File(path)
    }

    override fun serialize(encoder: Encoder, value: File) {
        listStringSerializer.serialize(encoder, listOf(value.toString()))
    }
}

private class ContractSourceSerializer : KSerializer<ContractSource> {
    override val descriptor: SerialDescriptor
        get() = buildClassSerialDescriptor("ContractSource") {
            element("content", PrimitiveSerialDescriptor("contentString", PrimitiveKind.STRING), isOptional = true)
            element("urls", FileSourceSerializer.descriptor, isOptional = true)
        }

    override fun deserialize(decoder: Decoder): ContractSource {
        var srcfile: File? = null
        var content: String? = null
        val dec = decoder.beginStructure(descriptor)
        var i = dec.decodeElementIndex(descriptor)
        while(i != CompositeDecoder.DECODE_DONE) {
            if(i == 0) {
                content = dec.decodeStringElement(descriptor, 0)
            } else if(i == 1) {
                srcfile = dec.decodeSerializableElement(descriptor, 1, FileSourceSerializer)
            } else {
                throw SerializationException("Unknown index $i")
            }
            i = dec.decodeElementIndex(descriptor)
        }
        dec.endStructure(descriptor)
        return ContractSource(
            content = content,
            srcFile = srcfile
        )
    }

    override fun serialize(encoder: Encoder, value: ContractSource) {
        val composite = encoder.beginStructure(descriptor)
        if(value.content != null) {
            composite.encodeStringElement(descriptor, 0, value.content)
        }
        if(value.srcFile != null) {
            composite.encodeSerializableElement(descriptor, 1, FileSourceSerializer, value.srcFile)
        }
        composite.endStructure(descriptor)
    }

}

@Serializable(with = ContractSourceSerializer::class)
data class ContractSource(
    val content: String? = null,
    val srcFile: File? = null
)