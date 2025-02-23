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
import spec.CVL

interface IContractLoader {
    fun load(sdc: ContractInstanceInSDC, cache: IPerContractClassCache) : IContractClass
    fun load(sdc: ContractInstanceInSDC) : IContractClass = this.load(sdc, cache = TrivialContractCache)
}

/**
 * A contract loader that knows how to ingest CVL information if available. It implements [IContractLoader]
 * and simply forwards to the [load] passing along null. It is expected that these loaders will be "curried" into
 * a real loader with [withQuery] below
 */
interface QueryAwareContractLoader : IContractLoader {
    override fun load(sdc: ContractInstanceInSDC, cache: IPerContractClassCache) : IContractClass = load(sdc, cache, null)
    fun load(sdc: ContractInstanceInSDC, cache: IPerContractClassCache, cvl: CVL?) : IContractClass
}

/**
 * "Curries" a [QueryAwareContractLoader] into a regular [IContractLoader], such that any load of a contract from the
 * loader will pass along the given [cvl] parameter to the receiver object.4
 */
fun QueryAwareContractLoader.withQuery(cvl: CVL?) = object : IContractLoader {
    override fun load(sdc: ContractInstanceInSDC, cache: IPerContractClassCache): IContractClass {
        return this@withQuery.load(sdc, cache, cvl)
    }
}
