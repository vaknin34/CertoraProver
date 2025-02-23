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
import tac.ICoreTACProgram
import tac.StorageUniverse
import tac.UnifiedSingleStorageUniverse
import tac.UnifiedStorageUniverse
import java.math.BigInteger

/**
 * A minimal scene that implements just what is needed for standalone type checking of specifications
 * code and TAC is not relevant here
 */
data class TrivialScene(
    val source: IContractSource,
    val loader: IContractLoader,
    val _contracts: List<ContractInstanceInSDC> = listOf(),
    override val forkInfo: IScene.ForkInfo = IScene.ForkInfo.BASE
): IScene {
    override fun getContractOrNull(s: NamedContractIdentifier): IContractClass? =
        _contracts.find { it.name == s.name }?.let { loader.load(it) }

    override fun getContractOrNull(a: BigInteger): IContractClass? {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun getMethods(sigHash: BigInteger): List<ITACMethod> {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun hasMethod(contractId: BigInteger, sigHash: BigInteger): Boolean {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun hasMethod(contractName: NamedContractIdentifier, sigHash: BigInteger): Boolean {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun getStorageUniverse(): StorageUniverse {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun getTransientStorageUniverse(): StorageUniverse {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun getUnifiedStorage(): UnifiedStorageUniverse {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun getUnifiedStorageInfoViewWithReadTrackers(): UnifiedSingleStorageUniverse {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun getContracts(): List<IContractClass> {
        return _contracts.map { loader.load(it) }
    }

    override fun getNonPrecompiledContracts(): List<IContractClass> {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun mapContractMethodsInPlace(sort: IScene.MapSort, transformId: String, p: (IScene, ITACMethod) -> Unit) {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun mapContractMethods(sort: IScene.MapSort, transformId: String, p: (IScene, ITACMethod) -> ICoreTACProgram) {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun mapContractsInPlace(sort: IScene.MapSort, transformId: String, p: (IScene, IContractClass) -> Unit) {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun mapScene(transformId: String, p: () -> Unit) {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun fork(forkInfo: IScene.ForkInfo): IScene {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }

    override fun getPrecompiledContracts(): List<IContractClass> {
        throw UnsupportedOperationException("TrivialScene only supports getContractOrNull(NamedContractIdentifier)")
    }
}
