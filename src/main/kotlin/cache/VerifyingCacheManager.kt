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

import cache.utils.ObjectSerialization
import java.io.BufferedInputStream
import java.io.BufferedOutputStream
import java.io.ByteArrayInputStream
import java.io.ByteArrayOutputStream


/**
 * A trivial cache that checks all cached objects are safely serializable and deserializable.
 *
 * In other words, this will always trigger a cache miss, but checks that the values to be cached
 * can be serialized without throwing an exception, and that the result of the serialization process
 * can be likewise safely deserialized. It does NOT check that the round trip is the identity function:
 * doing so would require consistent implementations of equals() which we do not yet have.
 */
object VerifyingCacheManager : ICacheManager {
    private fun <T> verifySerialization(o: T) {
        val baos = ByteArrayOutputStream()
        ObjectSerialization.writeObject(o, BufferedOutputStream(baos))
        val ser = baos.toByteArray()
        BufferedInputStream(ByteArrayInputStream(ser)).use {
            ObjectSerialization.readObject<T>(it)
        }
    }

    override fun <T> get(k: CacheKey): T? {
        return null
    }

    override fun <T> put(k: CacheKey, element: T): T? {
        verifySerialization(element)
        return element
    }

    override fun exists(k: CacheKey) = false

    override fun <T> getFromCache(k: CacheKey, missing: () -> T): T {
        val res = missing()
        verifySerialization(res)
        return res
    }

    override fun <T, U, R> withCache(k: CacheKey, missing: () -> U, fromCache: (T) -> R, toCache: (U) -> T, toResult: (U) -> R): R {
        val u = missing()
        verifySerialization(toCache(u))
        return toResult(u)
    }

    override fun <T, R> cacheUpdate(
        k: CacheKey,
        seed: T,
        update: (T) -> T,
        toCache: (T) -> R,
        fromCache: (T, R) -> T
    ): T {
        val up = update(seed)
        verifySerialization(toCache(up))
        return up
    }

    override fun <T, R> mergeWithCache(k: CacheKey, seed: R, merge: (R, T) -> R, toCache: (R) -> T): R {
        val x = toCache(seed)
        verifySerialization(x)
        return seed
    }

    override fun <R, O> getObjectStateManager(
        initialSeed: CacheKey,
        obj: O,
        save: () -> R,
        restore: (R) -> Unit
    ): ICacheManager.IObjectStateManager {
        return object : ICacheManager.IObjectStateManager {
            override fun transform(nextKey: CacheKey, f: () -> Unit) {
                f()
                verifySerialization(save())
            }

            override fun force() {
                // do nothing
            }

        }
    }
}
