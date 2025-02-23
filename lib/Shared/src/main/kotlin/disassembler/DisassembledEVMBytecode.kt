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

package disassembler

import com.certora.collect.*
import datastructures.stdcollections.*
import disassembler.*
import disassembler.EVMInstruction.*
import utils.*
import java.io.Serializable
import java.math.BigInteger

data class EVMCommand(val pc: EVMPC, val inst: EVMInstructionInfo, val meta: EVMMetaInfo): Serializable

/**
 * [bytecodeOriginal] - the original deployed bytecode
 * [bytecode] - the deployed bytecode without data and metadata sections
 * [auxdata] - the metadata section ("auxdata" in Solidity official terms)
 */
@Treapable
data class DisassembledEVMBytecode(
    val disassembledCode: Map<EVMPC, EVMCommand>,
    val bytes: List<UByte>, // All raw input bytes.  Broken down into code/auxdata below.
    val bytecodeHash: BigInteger,
    val auxdataStart: Int
) : Serializable {
    companion object {
        val empty = DisassembledEVMBytecode(mapOf(), listOf(), BigInteger.ZERO, 0)
    }
    override fun hashCode() = bytes.hashCode() // Everything else is derived from these bytes anyway

    val jumpDestPCs by lazy {
        disassembledCode.asSequence().filter { it.value.inst == JUMPDEST }.mapToTreapSet { it.key.toBigInteger() }
    }

    /** The "code" portion of the bytecode (prior to the auxdata) */
    val code: List<UByte> get() = bytes.subList(0, auxdataStart)
    /** The "data" portion of the bytecode */
    val auxdata: List<UByte> get() = bytes.subList(auxdataStart, bytes.size)

    /** List<UByte> is not serializable, so we translate to/from signed bytes for serialization. */
    private data class SerializableEVMBytecode(
        val disassembledCode: Map<EVMPC, EVMCommand>,
        val bytes: List<Byte>,
        val bytecodeHash: BigInteger,
        val auxdataStart: Int
    ) : Serializable {
        private fun readResolve(): Any? = DisassembledEVMBytecode(
            disassembledCode,
            bytes.map { it.toUByte() },
            bytecodeHash,
            auxdataStart
        )
    }

    private fun writeReplace(): Any? = SerializableEVMBytecode(
        disassembledCode,
        bytes.map { it.toByte() },
        bytecodeHash,
        auxdataStart
    )
}
