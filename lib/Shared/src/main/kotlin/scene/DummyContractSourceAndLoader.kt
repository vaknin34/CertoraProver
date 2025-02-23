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
import java.math.BigInteger

object DummyContractSourceAndLoader: IContractSource, IContractLoader {
    override fun instances(): List<ContractInstanceInSDC> = datastructures.stdcollections.emptyList()

    override fun aliases(): List<Set<BigInteger>> = datastructures.stdcollections.emptyList()
    override fun load(sdc: ContractInstanceInSDC, cache: IPerContractClassCache): IContractClass = throw IllegalStateException("No loading for dummy contract source and loader")

}
