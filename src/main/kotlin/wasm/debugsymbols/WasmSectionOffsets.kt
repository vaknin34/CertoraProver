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

package wasm.debugsymbols

import com.dylibso.chicory.wasm.Parser.readVarUInt32
import com.dylibso.chicory.wasm.exceptions.MalformedException
import com.dylibso.chicory.wasm.types.SectionId
import datastructures.stdcollections.*
import java.io.IOException
import java.io.InputStream
import java.nio.ByteBuffer
import java.nio.ByteOrder

/**
 * This class computes all section offsets for a wasm file. Also see https://webassembly.github.io/spec/core/binary/modules.html#sections
 *
 * [WasmDebugSymbols] requires the offset of the codeSection of a .wasm file.
 * With [getSectionOffsets] this class allows to load a .wasm file (as inputStream) and compute all section offsets.
 *
 * The Chicory Parser does this internally as well and the code is mostly take from https://github.com/dylibso/chicory/blob/main/wasm/src/main/java/com/dylibso/chicory/wasm/Parser.java.
 * Unfortunately, the section are only computed internally and not exposed via the class API. This also means, we need to read in the .wasm file a second time to
 * compute the offsets.
 */
object WasmSectionOffsets {
    private fun readByteBuffer(inputStream: InputStream): ByteBuffer {
        return try {
            val buffer = ByteBuffer.wrap(inputStream.readAllBytes())
            buffer.order(ByteOrder.LITTLE_ENDIAN)
            buffer
        } catch (var3: IOException) {
            throw IllegalArgumentException("Failed to read wasm bytes.", var3)
        }
    }

    private fun readInt(buffer: ByteBuffer): Int {
        return if (buffer.remaining() < 4) {
            throw MalformedException("length out of bounds")
        } else {
            buffer.getInt()
        }
    }

    private fun readByte(buffer: ByteBuffer): Byte {
        return if (!buffer.hasRemaining()) {
            throw MalformedException("length out of bounds")
        } else {
            buffer.get()
        }
    }

    fun getSectionOffsets(inputStream: InputStream): Map<Byte, Int> {
        val sectionOffsets = mutableMapOf<Byte, Int>()
        val buffer: ByteBuffer = readByteBuffer(inputStream)
        val magicNumber = readInt(buffer)
        if (magicNumber != 1836278016) {
            throw MalformedException("magic header not detected, found: $magicNumber expected: 1836278016")
        } else {
            val version = readInt(buffer)
            if (version != 1) {
                throw MalformedException("unknown binary version, found: $version expected: 1")
            } else {
                while (buffer.hasRemaining()) {
                    val sectionId = readByte(buffer)
                    val sectionSize = readVarUInt32(buffer);
                    when (sectionId) {
                        SectionId.TYPE.toByte(),
                        SectionId.IMPORT.toByte(),
                        SectionId.FUNCTION.toByte(),
                        SectionId.TABLE.toByte(),
                        SectionId.MEMORY.toByte(),
                        SectionId.GLOBAL.toByte(),
                        SectionId.EXPORT.toByte(),
                        SectionId.START.toByte(),
                        SectionId.ELEMENT.toByte(),
                        SectionId.CODE.toByte()->{
                            check(!sectionOffsets.containsKey(sectionId)){"The WASM file contains the section with id $sectionId twice. The WASM file is corrupt."}
                            sectionOffsets[sectionId] = buffer.position()
                        }
                        SectionId.CUSTOM.toByte() -> {
                            //There may be several custom sections, so we currently don't extract the beginning of these.
                        }
                    }
                    if(buffer.position() + sectionSize <= buffer.limit()) {
                        buffer.position(buffer.position() + sectionSize.toInt());
                    }
                }
            }
        }
        return sectionOffsets.toMap();
    }
}
