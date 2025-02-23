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

@file:UseSerializers(utils.BigIntegerSerializer::class)

package bridge

import datastructures.stdcollections.*
import kotlinx.serialization.Serializable
import kotlinx.serialization.UseSerializers
import utils.CertoraInternalErrorType
import utils.CertoraInternalException
import java.math.BigInteger

@Serializable
data class SingleDeployedContract( // this represents a solidity file with all its contracts. one may be marked primary
    val primary_contract: String,
    val primary_contract_address: BigInteger,
    val srclist: Map<String /*number*/, String>, // values will map to the fetched files' paths
    val sdc_name: String,
    val contracts: List<ContractInstanceInSDC>,
    val library_addresses: List<String/*address*/>,
    val state: Map<BigInteger /*number*/, BigInteger/*address*/> = mapOf(),
    val structLinkingInfo: Map<String, BigInteger> = mapOf(),
    val legacyStructLinking: Map<BigInteger, BigInteger> = mapOf(),
    val prototypeFor: List<String> = listOf(),
    val sourceDir: String, // must be specified in certoraBuild - subdirectory of .certora_sources to resolve against
    val origSourceDir: String, // must be specified in certoraBuild, see above
) {
    fun primaryContractInstance(): ContractInstanceInSDC {
        return contracts.find { contractInstance -> contractInstance.name == primary_contract }
            ?: throw CertoraInternalException(
                CertoraInternalErrorType.SOLC_INTERFACE,
                "primary contract $primary_contract not listed in contracts of $this"
            )
    }

    fun parseSourceList() = srclist.mapKeys {
        it.key.toIntOrNull()
            ?: throw CertoraInternalException(
                CertoraInternalErrorType.SOLC_INTERFACE,
                "Invalid srclist for SDC. got: $srclist"
            )
    }
}
