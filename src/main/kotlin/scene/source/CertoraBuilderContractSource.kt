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

package scene.source

import bridge.BuildConf
import bridge.ContractInstanceInSDC
import bridge.sortContractsByStateLinks

open class CertoraBuilderContractSource(val buildConf: BuildConf) : IContractSourceFull {
    // add primary contracts
    private val contracts = buildConf.values.map { singleDeployedContract ->
        singleDeployedContract.primaryContractInstance().withDataOfSDC(singleDeployedContract)
    }.let { unsortedContracts ->
        sortContractsByStateLinks(unsortedContracts)
    }

    override fun fullInstances(): List<ContractInstanceInSDC> = buildConf.values.flatMap { singleDeployedContract ->
        singleDeployedContract.contracts.map { it.withDataOfSDC(singleDeployedContract) }
    }

    override fun instances(): List<ContractInstanceInSDC> {
        return contracts
    }

}
