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

package scene.loader

import bridge.ContractInstanceInSDC
import scene.IContractClass
import scene.IContractLoader
import scene.IPerContractClassCache
import scene.QueryAwareContractLoader
import spec.CVL
import java.util.concurrent.ConcurrentHashMap

/*
  Does not interact with the on-disk cache
 */
class CachingContractLoader(val wrapped: IContractLoader) : IContractLoader {
    private val memCache = ConcurrentHashMap<ContractInstanceInSDC, IContractClass>()
    override fun load(sdc: ContractInstanceInSDC, cache: IPerContractClassCache): IContractClass =
      if (memCache.containsKey(sdc)) {
        memCache[sdc]!!
      } else {
        val iContractClass = wrapped.load(sdc, cache)
        memCache[sdc] = iContractClass
        iContractClass
      }
}

class QueryAwareCachingLoader(val wrapped: QueryAwareContractLoader) : QueryAwareContractLoader {
    private val memCache = ConcurrentHashMap<ContractInstanceInSDC, IContractClass>()
    override fun load(sdc: ContractInstanceInSDC, cache: IPerContractClassCache, cvl: CVL?): IContractClass =
        if (memCache.containsKey(sdc)) {
            memCache[sdc]!!
        } else {
            val iContractClass = wrapped.load(sdc, cache, cvl)
            memCache[sdc] = iContractClass
            iContractClass
        }

}

fun IContractLoader.caching() = if(this is CachingContractLoader) this else CachingContractLoader(this)
fun QueryAwareContractLoader.caching() = if(this is QueryAwareCachingLoader) this else QueryAwareCachingLoader(this)
