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

import bridge.NamedContractIdentifier
import config.Config
import datastructures.stdcollections.*
import instrumentation.createContractClassWithoutMethods
import instrumentation.createEmptyProgram
import parallel.ParallelPool
import parallel.ParallelPool.Companion.runInherit
import parallel.Scheduler.compute
import parallel.forkEvery
import parallel.pcompute
import statistics.RunIDFactory
import tac.*
import utils.toLeft
import utils.toRight
import utils.toValue
import vc.data.StorageInfo
import vc.data.StorageInfoWithReadTracker
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * See [IScene].
 */
class Scene(
    private val source: IContractSource,
    private val contractLoader: IContractLoader,
    override val forkInfo: IScene.ForkInfo = IScene.ForkInfo.BASE,
    private val dynamicContracts: MutableList<BigInteger> = mutableListOf(),
) : IDynamicScene, ExtendableScene {
    constructor(
        source: IContractSource,
        contractLoader: IContractLoader,
        forkInfo: IScene.ForkInfo = IScene.ForkInfo.BASE
    ) : this(source, contractLoader, forkInfo, mutableListOf<BigInteger>())

    private val contracts: MutableList<IContractClass> = mutableListOf()
    private val precompiled = getPrecompiledContracts()
    private val addressesAliases: MutableList<Set<BigInteger>> =
        dynamicContracts.mapTo(getAliasesFromInstances().toMutableList()) {
            setOf(it)
        }

    private fun getAliasesFromInstances() = source.aliases()

    private var loaded = false
    fun load() {
        contracts.addAll(source.instances().forkEvery { instance ->
            compute { contractLoader.load(instance) }
        }.pcompute().map { lst ->
            lst.distinctBy {
                if(Config.EnableSimpleContractMatching.get()) {
                    it.name
                } else {
                    it.instanceId
                }
            }
        }.runInherit())
        loaded = true
    }

    init {
        RunIDFactory.runId().reportScene(this) //Collect contracts' identifier info
    }

    override fun extendContractWith(target: NamedContractIdentifier, m: List<TACMethod>) {
        if(!loaded) {
            load()
        }
        val toWriteLoc = contracts.indexOfFirst {
            it.name == target.name
        }.takeIf { it >= 0 } ?: error("can't find ${target.name} in the scene")
        val contract = contracts[toWriteLoc]
        contracts[toWriteLoc] = contract.extendWith(m)
    }

    override fun getContracts(): List<IContractClass> {
        if (!loaded) {
            load()
        }
        return contracts
    }

    override fun getContractOrNull(s: NamedContractIdentifier): IContractClass? {
        if (!loaded) {
            load()
        }
        return contracts.find { it.name == s.name }
    }

    private fun getContractImpl(a: BigInteger): utils.Either<IContractClass, String> {
        if (!loaded) {
            load()
        }
        precompiled.find { it.instanceId == a }?.let { return it.toLeft() }

        val aliasedContractInstance = addressesAliases.find { a in it }
            ?: return "Asked for non-existing contract with instanceId $a, not even another contract with same bytecode and different instanceId has been found.".toRight()
        return contracts.find { it.instanceId in aliasedContractInstance }?.toLeft()
            ?: "Asked for non-existing contract with instanceId $a".toRight()
    }

    override fun getContractOrNull(a: BigInteger): IContractClass? = getContractImpl(a).toValue({ it }) { null }

    override fun getContract(a: BigInteger): IContractClass = getContractImpl(a).toValue({ it }) {
        throw SceneQueryException(it)
    }

    override fun getMethods(sigHash: BigInteger): List<ITACMethod> {
        if (!loaded) {
            load()
        }
        return contracts.mapNotNull { it.getMethodBySigHash(sigHash) }
    }

    override fun mapContractMethodsInPlace(sort: IScene.MapSort, transformId: String, p: (IScene, ITACMethod) -> Unit) {
        if (!loaded) {
            load()
        }
        mapEachContract(sort) { c ->
            c.mapMethodsInPlace(sort, this, p)
        }
    }

    /**
     * applies the [cb] on every contract in the Scene as determined by the [sort] `MapSort` - i.e. in parallel or sequentially
     */
    private fun mapEachContract(sort: IScene.MapSort, cb: (IContractClass) -> Unit) {
        if(sort == IScene.MapSort.PARALLEL) {
            contracts.forkEvery {
                compute {
                    cb(it)
                }
            }.pcompute().runInherit(ParallelPool.SpawnPolicy.GLOBAL)
        } else {
            contracts.forEach {
                cb(it)
            }
        }
    }

    override fun mapContractMethods(sort: IScene.MapSort, transformId: String, p: (IScene, ITACMethod) -> ICoreTACProgram) {
        if (!loaded) {
            load()
        }
        mapEachContract(sort) { c ->
            c.mapMethods(sort, this, p)
        }
    }

    override fun mapContractsInPlace(sort: IScene.MapSort, transformId: String, p: (IScene, IContractClass) -> Unit) {
        if (!loaded) {
            load()
        }
        mapEachContract(sort) {
            p(this, it)
        }
    }

    override fun mapScene(transformId: String, p: () -> Unit) {
        p()
    }

    override fun getStorageUniverse(): StorageUniverse {
        return getContracts().associate { it.instanceId to it.storage }
    }

    override fun getTransientStorageUniverse(): StorageUniverse {
        return getContracts().associate { it.instanceId to it.transientStorage }
    }

    override fun getUnifiedStorageInfoViewWithReadTrackers(): UnifiedSingleStorageUniverse {
        val ret = mutableMapOf<BigInteger, StorageInfoWithReadTracker>()
        getUnifiedStorage().forEachEntry { (instanceId, unifiedStorageInfo) ->
            val persistentVars = (unifiedStorageInfo.persistentStorageInfo as StorageInfoWithReadTracker).storageVariables
            val transientVars = (unifiedStorageInfo.transientStorageInfo as StorageInfo).withDummyReadTrackers().storageVariables
            check(transientVars.keys.none { it in persistentVars.keys }) { "Not expecting to find shared variables in the StorageInfo objects of persistent and transient storages" }
            ret[instanceId] = StorageInfoWithReadTracker(persistentVars + transientVars)
        }
        return ret
    }

    override fun getContractUniverse(): ContractUniverse = source.contractUniverse()

    override fun fork(forkInfo: IScene.ForkInfo): Scene {
        // deep-copy the contracts
        val newScene = Scene(source, contractLoader, forkInfo, dynamicContracts.toMutableList())
        newScene.loaded = true // we don't want to load again
        newScene.contracts.clear()
        newScene.contracts.addAll(contracts.map { it.fork() })
        return newScene
    }

    override fun getPrecompiledContracts(): List<IContractClass> {
        return getPrecompiled(getContractUniverse())
    }

    override fun cloneContract(contract: IContractClass): IClonedContract {
        val freshInstanceId = this.getFreshInstanceId()
        val freshContract = contract.cloneTo(freshInstanceId)
        contracts.add(freshContract)
        dynamicContracts.add(freshInstanceId)
        addressesAliases.add(setOf(freshInstanceId))
        return freshContract
    }
}

internal fun getPrecompiled(cu: ContractUniverse): List<IContractClass> {
    val ret = mutableListOf<IContractClass>()
    if (cu == ContractUniverse.ETHEREUM) {
        // add synthetic contracts for precompiled contracts
        for (i in cu.addresses) {
            val name = cu.getNameOfPrecompiledByAddress(i) ?: "Precompiled$i"
            val precompiled = PrecompiledContractCode.getPrecompiledImplemented(i)
            val precompiledContract = precompiled?.contract
                ?: createContractClassWithoutMethods(
                    name,
                    i,
                    TACSymbol.Const(i, Tag.Bit256),
                    createEmptyProgram(name)
                )
            ret.add(precompiledContract)
        }
    }
    return ret
}
