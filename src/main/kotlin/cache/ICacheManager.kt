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

import config.Config

/**
 * An object which manages a cache keyed by instances of [CacheKey]
 */
interface ICacheManager {
    /**
     * Get an object within the cache keyed by [k], return null if missing
     */
    fun <T> get(k: CacheKey): T?

    /**
     * Put an object in the cache under [k]. If an entry exists for [k], return the previous object,
     * otherwise return null
     */
    fun <T> put(k: CacheKey, element: T): T?

    /**
     * Check if there is an object in the cache keyed by [k]
     */
    fun exists(k: CacheKey): Boolean

    /**
     * Get an object within the cache keyed by [k], computing missing results with [missing].
     *
     * Implementations may cache the result of [missing] under [k].
     */
    fun <T> getFromCache(k: CacheKey, missing: () -> T) : T

    /**
     * A general form of [getFromCache]. Read value of type [T] from the cache as keyed by [k]. Upon cache hit,
     * transform the result to [R] via [fromCache].
     *
     * Upon a cache miss, compute a value of type [U] via [missing]. Implementations may optionally populate the
     * cache under [k] with a value of type [T] via the [toCache] method. The value of type [U] is then
     * transformed to a result with [toResult].
     *
     * It is expected (but not checked) that the following property holds:
     *
     * toResult(missing()) == fromCache(toCache(missing()))
     */
    fun <T, U, R> withCache(k: CacheKey, missing: () -> U, fromCache: (T) -> R, toCache: (U) -> T, toResult: (U) -> R) : R

    fun <T, R> cacheUpdate(k: CacheKey, seed: T, update: (T) -> T, toCache: (T) -> R, fromCache: (T, R) -> T): T

    /**
     * On cache hit, with a given [seed], read a value of type [T] from the cache (id'd by [k]) and merge it with the seed via [merge].
     * Then store the result of the merged with [toCache]. Then returns the result of the merge.
     *
     * On a cache miss, the cache may be optionall populated with the result of toCache(seed).
     *
     * This is used to cache side-effects; it is not ideal and should be used sparingly.
     */
    fun <T, R> mergeWithCache(k: CacheKey, seed: R, merge: (R, T) -> R, toCache: (R) -> T): R

    fun <R, O> getObjectStateManager(initialSeed: CacheKey, obj: O, save: () -> R, restore: (R) -> Unit) : IObjectStateManager

    /**
     * A state manager for the CacheManager whose role
     * is to optionally apply transformations,
     * while taking into account the possibilities to skip
     * some of those transformations by querying their results from the cache.
     */
    interface IObjectStateManager {
        /**
         * [nextKey] is the cache key of the result of the transformation [f].
         * [f] is the transformation we want to apply.
         */
        fun transform(nextKey: CacheKey, f: () -> Unit)

        /**
         * Used to query the cache, in some given context.
         */
        fun force()
    }

    companion object {
        operator fun invoke() =
            if (Config.getIsUseCache()) {
                CacheManager(Config.CacheDirName.get())
            } else if (Config.VerifyCache.get()) {
                VerifyingCacheManager
            } else {
                NullCache
            }
    }
}

object NullCache : ICacheManager {
//    override fun <T> getOrPut(k: CacheKey, missing: () -> T): T = missing()

    override fun <T> get(k: CacheKey): T? = null

    override fun <T> put(k: CacheKey, element: T) = null

    override fun <T, U, R> withCache(
        k: CacheKey,
        missing: () -> U,
        fromCache: (T) -> R,
        toCache: (U) -> T,
        toResult: (U) -> R
    ): R = toResult(missing())

    override fun <T> getFromCache(k: CacheKey, missing: () -> T) = missing()

    override fun exists(k: CacheKey) = false

    override fun <T, R> cacheUpdate(k: CacheKey, seed: T, update: (T) -> T, toCache: (T) -> R, fromCache: (T, R) -> T) =
        update(seed)

    override fun <T, R> mergeWithCache(k: CacheKey, seed: R, merge: (R, T) -> R, toCache: (R) -> T) =
        merge(seed, toCache(seed))

    override fun <R, O> getObjectStateManager(
        initialSeed: CacheKey,
        obj: O,
        save: () -> R,
        restore: (R) -> Unit
    ): ICacheManager.IObjectStateManager {
        return object : ICacheManager.IObjectStateManager {
            override fun transform(nextKey: CacheKey, f: () -> Unit) {
                f()
            }

            override fun force() {

            }

        }
    }
}
