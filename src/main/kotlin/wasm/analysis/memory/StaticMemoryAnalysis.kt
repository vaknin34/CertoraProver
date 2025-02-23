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

package wasm.analysis.memory

import utils.*
import vc.data.CoreTACProgram
import wasm.analysis.memory.IMemoryPartitions.*
import wasm.ir.WasmData
import wasm.ir.WasmProgram
import java.math.BigInteger

/**
 * Allows directly reading the contents of initialized memory (when the memory is provably read-only)
 *
 * [ctp] should be the TAC representation of [program]
 */
class StaticMemoryAnalysis(
    val program: WasmProgram,
    val ctp: CoreTACProgram,
    private val permissions: IMemoryPartitions
) {

    private val datas = program.fields.filterIsInstance<WasmData>()

    private fun dataForAddress(address: BigInteger, datas: List<WasmData>): Pair<WasmData, Int>? =
        datas.mapNotNull {
            it `to?` it.indexOfAddress(address)
        }.uniqueOrNull()

    /**
     * @return the bytes stored at [address, address+size) if this range is read only in [ctp]
     */
    fun readBytes(address: BigInteger, size: Int): List<UByte>? {
        if (permissions.permission(address, address+size.toBigInteger() - BigInteger.ONE) != Permission.ReadOnly) {
            return null
        }

        val (data, idx) = dataForAddress(address, datas) ?: return null

        if (idx + size - 1 >= data.content.size) {
            return null
        }

        return data.content.subList(idx, idx + size)
    }

    /**
     * @return the bytes stored at [address, address+size) interpreted as a little-endian word
     *         if this range is read only in [ctp]
     */
    fun readLittleEndianWord(address: BigInteger, size: Int): BigInteger? = readBytes(address, size)?.reversed()?.toPositiveBigIntegerOrNull()

    /**
     * @return the bytes stored at [address, address+size) interpreted as a little-endian 32-bit word
     *         if this range is read only in [ctp]
     */
    fun readLittleEndian32BitWord(address: BigInteger) = readLittleEndianWord(address, 4)
}
