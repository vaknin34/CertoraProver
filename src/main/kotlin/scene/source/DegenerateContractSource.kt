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

import bridge.ContractInstanceInSDC
import scene.*

class DegenerateContractSource(val inputFile: String) : IContractSourceFull, IContractLoader {
    override fun instances(): List<ContractInstanceInSDC> {
        return listOf()
    }

    override fun contractUniverse(): ContractUniverse = ContractUniverse.ETHEREUM // Unless otherwise specified...

    override fun load(sdc: ContractInstanceInSDC, cache: IPerContractClassCache): IContractClass {
        check(sdc == instances().firstOrNull()) { "Can't load a different contract instance than the one generated for $inputFile" }
        return DegeneratedContractClass
    }

    override fun fullInstances(): List<ContractInstanceInSDC> = instances()
}
