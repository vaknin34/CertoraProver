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

package cache

/**
 * Will force the loading of methods specified in the system property `cvt.force.load`, but use the cache for everything
 * else. The format of methods is a sequence of `ContractClass:methodName` tuples, separated by `,`. The method name
 * should not contain the argument types.
 */
class PerMethodLoadPolicy : CachePolicy {

    private val toForce = System.getProperty("cvt.force.load", "").split(",").mapNotNull {
        it.split(":").takeIf {
            it.size == 2
        }?.let {
            it[0] to it[1]
        }
    }.groupBy({
        it.first
    }, { it.second }).mapValues { it.value.toSet() }

    override fun useCache(h: TransformationHistory): Boolean {
        return h != TransformationHistory.InitialLoad
    }

    override fun useCache(load: ContractLoad): Boolean {
        val methodName = when(load.component) {
            is ContractLoad.Component.MethodLoad -> load.component.methodName
            is ContractLoad.Component.MethodDecompile -> load.component.methodName
            is ContractLoad.Component.Decompilation -> return load.contract !in toForce
            else -> return true
        }
        return toForce[load.contract]?.let {
            methodName !in it
        } ?: true
    }
}
