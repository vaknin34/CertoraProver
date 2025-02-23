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

package spec

import spec.cvlast.CVLType
import spec.cvlast.ContractAliasDefinition
import spec.cvlast.SolidityContract
import spec.cvlast.SortDeclaration
import spec.cvlast.typechecker.CVLError
import spec.cvlast.typedescriptors.VMTypeDescriptor
import utils.CollectingResult
import utils.VoidResult

interface TypeResolver {
    val factory: VMDescriptorFactory

    fun resolveVMType(contractName: String?, typeName: String, location: String?) : CollectingResult<VMTypeDescriptor, String>
    fun resolveCVLType(contract: String?, id: String): CollectingResult<CVLType.PureCVLType, String>
    fun registerContractAlias(alias: ContractAliasDefinition): VoidResult<CVLError>

    fun resolveContractName(contract: String): String

    fun resolveNameToContract(contract: String): SolidityContract

    fun registerSorts(s: List<SortDeclaration>)

    fun clone(): TypeResolver
    fun validContract(contractName: String): Boolean
}
