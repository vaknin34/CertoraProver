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

package scene

import bridge.ContractInstanceInSDC
import bridge.NamedContractIdentifier
import datastructures.stdcollections.*

/**
 * A mapping from base contracts to the list of [ExtensionInfo]: contracts that extend them and a list of functions to
 * exclude from the extension process (to avoid duplicate functions in the base contract).
 */
data class ExtensionContractsMapping (
    private val mapping: Map<NamedContractIdentifier, List<ExtensionInfo>>
) : Map<NamedContractIdentifier, List<ExtensionContractsMapping.ExtensionInfo>> by mapping {
    data class ExtensionInfo(
        val extensionContract: NamedContractIdentifier,
        val funcsToExclude: Set<String>,
    )

    companion object {
        fun fromContracts(contracts: List<ContractInstanceInSDC>): ExtensionContractsMapping {
            val mergeMap = contracts.mapNotNull { contract ->
                if (contract.extensionContracts.isEmpty()) {
                    return@mapNotNull null
                }
                NamedContractIdentifier(contract.name) to contract.extensionContracts.map { ext ->
                    ExtensionInfo(NamedContractIdentifier(ext.extension.name), ext.exclusion)
                }
            }.toMap()

            return ExtensionContractsMapping(mergeMap)
        }
    }
}
