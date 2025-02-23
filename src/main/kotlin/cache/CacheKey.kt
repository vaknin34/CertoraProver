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

import log.Logger
import log.LoggerTypes
import utils.toHexString
import java.math.BigInteger
import java.security.MessageDigest

private val logger = Logger(LoggerTypes.CACHE)

private val sep = "SEP".toByteArray()

val dig = object : ThreadLocal<MessageDigest>() {
    override fun initialValue(): MessageDigest {
        return MessageDigest.getInstance("SHA-256")
    }
}

private fun extendHash(base: String, nxt: String) : String = extendHash(base, nxt.toByteArray())

private fun extendHash(base: String, nxt: ByteArray) : String {
    val m = dig.get()
    m.update(base.toByteArray())
    m.update(sep)
    val hash = m.digest(nxt)
    return hash.toHexString()
}

/**
 * A wrapper around a cache key. Each cache key represents a state of the cache, and can be extended
 * via [extend] to yield a sub-key within the cache. The [extend] function is also used to represent
 * evolving cache state; this should be kept distinct from keys used to "index" into the cache.
 *
 * Extending the hash involves hashing a byte array with SHA-256.
 */
@JvmInline
value class CacheKey(val wrapped: String) {
    fun extend(p: String): CacheKey {
        return CacheKey(extendHash(wrapped, p)).also {
            logger.debug { "Extending $this with $p, getting $it" }
        }
    }

    fun extend(p: BigInteger) : CacheKey {
        return CacheKey(extendHash(wrapped, p.toByteArray())).also {
            logger.debug { "Extending $this with ${p.toString(16)}, getting $it" }
        }
    }
}
