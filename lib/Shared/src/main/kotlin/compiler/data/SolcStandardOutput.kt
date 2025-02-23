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

import compiler.ABI
import bridge.StorageLayout
import kotlinx.serialization.Serializable
import kotlinx.serialization.json.JsonObject

@Serializable
data class Output(
        val errors: List<Error> = listOf(),
        val contracts: Map<String, ContractFile> = mapOf(),
        val sources: Map<String, SourceParsed> = mapOf()
)

@Serializable
data class Error(
        val sourceLocation: SourceLocation,
        val type: String,
        val message: String,
        val severity: String
)

@Serializable
data class SourceParsed(
        val ast: JsonObject
)

@Serializable
class SourceLocation(
        val file: String,
        val start: Int,
        val end: Int
)

typealias ContractFile = Map<String, Contract>

@Serializable
data class Contract(
        val evm: ContractEVM = ContractEVM(),
        val abi: List<ABI> = listOf(),
        val storageLayout: StorageLayout? = null,
        val transientStorageLayout: StorageLayout? = null
)

@Serializable
data class ContractEVM(
        val bytecode: EVMBytecode = EVMBytecode(),
        val deployedBytecode: EVMBytecode = EVMBytecode(),
        val methodIdentifiers: Map<String, String> = mapOf()
)

@Serializable
data class EVMBytecode(
        val `object`: String? = null,
        val sourceMap: String? = null
)
