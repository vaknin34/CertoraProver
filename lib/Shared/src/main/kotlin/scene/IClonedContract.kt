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

import java.math.BigInteger

interface IClonedContract : IContractClass {
    /**
     * The id of the contract this contract was cloned from
     */
    val sourceContractId: BigInteger

    /**
     * This contract is the nth clone of [sourceContractId], where n is [createdContractInstance]. Different clones
     * must have different values of [createdContractInstance]. This provides a total (but completely) arbitrary
     * order on the cloned instances of [sourceContractId], which is convenient for generating instantiation code.
     */
    var createdContractInstance: Int
}
