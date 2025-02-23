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

import certora.CVTVersion
import com.certora.collect.*
import config.*
import datastructures.stdcollections.*
import log.Logger
import log.LoggerTypes
import scene.ICacheAwareSource
import scene.IContractSource
import utils.*
import java.io.Serializable
import java.math.BigInteger
import java.util.*

private val logger = Logger(LoggerTypes.CACHE)

@Treapable
private object MISSING : Serializable {
    private fun readResolve(): Any = MISSING
    override fun hashCode(): Int = utils.hashObject(this)

    override fun toString(): String {
        return "!MISSING!"
    }
}

private const val versionNumber = 5

class StandardCache(val wrapped: IContractSource) : IContractSource by wrapped, ICacheAwareSource {
    companion object {
        private fun getDeployKey(): String {
            return this::class.java.classLoader.getResourceAsStream("certora.properties")?.let {
                val p = Properties()
                try {
                    p.load(it)
                    p
                } catch (_: Exception) {
                    null
                }
            }?.getProperty("certora.cvt.deploy-seed")
                ?.also { logger.info { "Got deploy key from deploy-seed property $it" } }
                ?: CVTVersion.getInternalVersionString()
                    .also { logger.info { "Got deploy key from internal version string $it" } }
        }

        val baseCacheKey: ByteArray by lazy {
            digestItems(
                baseDigestItems() + digestConfig { it !is TransformationAgnosticConfig }
            )
        }

        val baseCacheKeyForRuleLevelCache: ByteArray by lazy {
            digestItems(baseDigestItems() + digestConfig { it !is RuleCacheAgnosticConfig })
        }

        fun baseDigestItems() = listOf(
            Config.CacheKeyName.get().also { logger.info { "chaining cache key name $it" } },
            versionNumber.also { logger.info { "chaining version number $it" } },
            getDeployKey().also { logger.info { "chaining deploy key $it" } },
        )

        fun digestConfig(filterConfigs: (ConfigType<*>) -> Boolean) =
            ConfigRegister.registeredConfigs.toList().sortedBy { it.name }
                .filter(filterConfigs)
                .also {
                    logger.info {
                        "Configs order: ${
                            it.joinToString(",") { c ->
                                val v = c.getOrNull()?.let {
                                    if(it is Array<*>) {
                                        it.contentDeepToString()
                                    } else {
                                        it.toString()
                                    }
                                } ?: MISSING
                                "${c.name} -> $v -> ${withStringDigest { it.writeObject(v) }}"
                            }
                        }"
                    }
                }
                .map { it.getOrNull() ?: MISSING }
    }

    override val baseCacheKey: BigInteger
        get() = if (wrapped is ICacheAwareSource) {
            digestItems(listOf(Companion.baseCacheKey, wrapped.baseCacheKey))
        } else {
            Companion.baseCacheKey
        }.let(::BigInteger).also { logger.info { "Base cache key $it" } }
}

fun IContractSource.withCache(): ICacheAwareSource = StandardCache(this)
