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
import config.Config
import event.CacheEvent
import log.Logger
import log.LoggerTypes
import report.CVTSystemEventsReporter
import vc.data.CoreTACProgram
import verifier.ChainedCodeTransformers
import java.io.BufferedOutputStream
import java.io.File
import java.io.FileOutputStream
import java.io.Serializable
import java.nio.file.Files
import java.nio.file.Paths
import java.util.concurrent.atomic.AtomicBoolean

private val logger = Logger(LoggerTypes.CACHE)

/**
 * A cache manager which stores serialized objects under [ cachePath]
 *
 * CONCURRENCY NOTE:
 * All CacheManagers have a common state, as a temporary hack. This might be confusing.
 * Careful when using in unit tests.
 */
class CacheManager(cachePath: String) : ICacheManager, Serializable {
    private val cacheDir = Paths.get(cachePath)
    /**
     * These fields are used as a needed workaround because of the cache
     * eviction strategy in prover.py
     * Currently, if files are written to the cache, all the "old" files
     * get deleted. To avoid this, when there is a cache write, we also touch
     * all the files for which there was a cache hit, so they will not get deleted.
     * TODO: remove when cache deletion in prover.py is revamped. See Jira ticket https://certora.atlassian.net/browse/CERT-1759
     */

    companion object {
        private val cacheHitFilesNames : MutableSet<File> = datastructures.stdcollections.mutableSetOf()
        private val cacheWrite : AtomicBoolean = AtomicBoolean() // true if there's been a cache write
    }

    init {
        val f = cacheDir.toFile()
        if(!f.exists()) {
            try {
                Files.createDirectories(cacheDir)
            } catch(x: java.lang.Exception) {
                logger.warn(x) {
                    "Failed to create cache directory, cache will not be used"
                }
            }
        }
        if(f.exists()) {
            logger.info {
                "Using cache at $cacheDir"
            }
        }
    }

    private fun <T> cacheSaneWithFallback(fallback: () -> T, sane: () -> T) : T {
        return if(cacheDir.toFile().exists() && cacheDir.toFile().isDirectory) {
            sane()
        } else {
            logger.info { "Cache directory $cacheDir does not exist or is not a directory, recomputing" }
            fallback.invoke()
        }
    }

    override fun <T, U, R> withCache(k: CacheKey, missing: () -> U, fromCache: (T) -> R, toCache: (U) -> T, toResult: (U) -> R) : R {
        return cacheSaneWithFallback({
            toResult(missing.invoke())
        }) {
            readFromCache<T>(k)?.let{fromCache(it)}?:run{
                val f = cacheDir.resolve(k.wrapped).toFile()
                if (Config.AssertCacheHits.get()) {
                    throw IllegalArgumentException("Expected the cache to hit on ${k.wrapped} but it missed")
                }
                val r = missing()
                try {
                    val cacheItem = toCache(r)
                    BufferedOutputStream(FileOutputStream(f)).use { out ->
                        ObjectSerialization.writeObject(obj = cacheItem, out)
                    }
                    markCacheWrite()
                    logger.info { "wrote cache key ${k.wrapped} to file ${f.name}" }

                } catch (e: Exception) {
                    logger.warn(e) {
                        "Failed trying to write cache..."
                    }
                }
                toResult(r)
            }
        }
    }

    /**
     * If there was a cache write, mark all the files for which there were cache hit as modified.
     * This workaround is needed so these files will not be deleted while running in cloud env.
     */
    private fun markCacheWrite() {
        if (cacheWrite.get()) return
        synchronized(Companion) {
            if (!cacheWrite.get()) {
                cacheWrite.set(true)
                logger.info { "markCacheWrite() first cache write. cacheHitsFile size is ${cacheHitFilesNames.size}" }
                cacheHitFilesNames.forEach { touchFile(it) }
                cacheHitFilesNames.clear()
            }
        }

    }

    private fun <T> readFromCache(k: CacheKey): T? {
        val f = cacheDir.resolve(k.wrapped).toFile()
        if (f.exists() && f.isFile && f.canRead()) {
            logger.info { "Cache hit for key ${k.wrapped}" }
            CacheEvent.CacheHit(k.wrapped).emit(CVTSystemEventsReporter)
            return try {
                touchFileIfNeeded(f)
                ObjectSerialization.readObject<T>(f)
            } catch (e: Exception) {
                logger.warn(e) {
                    "Failed trying to read from cache ${k.wrapped} - ${e.message}"
                }
                if (Config.AssertCacheHits.get()) {
                    throw IllegalArgumentException("Expected the cache to hit on ${k.wrapped} but it failed to read from the cache")
                }
                null
            }
        }
        else
        {
            logger.info { "Cache miss for key ${k.wrapped}" }
            CacheEvent.CacheMiss(k.wrapped).emit(CVTSystemEventsReporter)
            return null
        }
    }

    private fun touchFileIfNeeded(f: File) {
        if (cacheWrite.get()) {
            touchFile(f)
        } else {
            synchronized(Companion) {
                if (cacheWrite.get()) {
                    touchFile(f)
                } else {
                    cacheHitFilesNames.add(f)
                    logger.debug { "adding to cacheHitsFile: $f - current size: ${cacheHitFilesNames.size}" }
                }
            }
        }
    }

    override fun <T, R> cacheUpdate(
        k: CacheKey,
        seed: T,
        update: (T) -> T,
        toCache: (T) -> R,
        fromCache: (T, R) -> T,
    ): T {
        return withCache(k, missing = {
            update(seed)
        }, toCache = {
            toCache(it)
        }, fromCache = {
            fromCache(seed, it)
        }, toResult = {
            it
        })
    }

    override fun <T, R> mergeWithCache(k: CacheKey, seed: R, merge: (R, T) -> R, toCache: (R) -> T): R {
        return withCache(k, missing = { seed }, toCache = toCache, toResult = {it}, fromCache = {
            merge(seed, it)
        })
    }

    override fun <R, O> getObjectStateManager(
        initialSeed: CacheKey,
        obj: O,
        save: () -> R,
        restore: (R) -> Unit
    ): ICacheManager.IObjectStateManager {

        return object : ICacheManager.IObjectStateManager {
            // are we in a state where a loading from the cache is needed?
            var needLoad = false
            var currKey = initialSeed
            /**
             * The idea is that we want to load from the cache only objects that will actually be used.
             * Suppose we have a set of transformations, applied one after the other (as done for example,
             * when a [ChainedCodeTransformers] is used).
             * We want to skip computing transformations if their results may be fetched from the cache.
             * But we don't want to load such a result of a transformation from the cache, if right after that, comes another transformation
             * which its result can be also fetched from the cache. This will make the previous cache load redundant.
             */
            override fun transform(nextKey: CacheKey, f: () -> Unit) {
                if (!exists(nextKey)) {
                    force()
                    withCache(k = nextKey, missing = {
                        f()
                        obj
                    }, toCache = {
                        save()
                    }, fromCache = {
                        restore(it)
                    }, toResult = {
                        Unit
                    })
                    currKey = nextKey
                    // the result of [f] applied on [nextKey] is not in the cache
                    needLoad = false
                } else {
                    // the results of [f] applied on [nextKey] is in the cache
                    needLoad = true
                    currKey = nextKey
                }
            }

            override fun force() {
                if (needLoad) {
                    restore(get<R>(currKey)!!)
                    needLoad = false
                }
            }
        }
    }

    private fun <T> ifCacheLive(k: CacheKey, missing: () -> T): T {
        return withCache(k, missing, toCache = {it}, fromCache = {it}, toResult = {it})
    }

    override fun <T> get(k: CacheKey): T? {
        return readFromCache(k)
    }

    override fun <T> put(k: CacheKey, element: T): T? {
        val lastVal : T? = readFromCache(k)
        cacheUpdate(k, element, { it}, { it}, { _, it -> it})
        return lastVal
    }

    override fun exists(k: CacheKey): Boolean {
        val f = cacheDir.resolve(k.wrapped).toFile()
        if (f.exists() && f.isFile && f.canRead()) {
            touchFileIfNeeded(f)
            return true
        }
        return false
    }

    override fun <T> getFromCache(k: CacheKey, missing: () -> T): T {
        return cacheSaneWithFallback(missing) {
            ifCacheLive(k, missing)
        }
    }

    private fun touchFile(f : File) {
        try {
            f.setLastModified(System.currentTimeMillis()).also { logger.debug {  "delete cache = ${Config.DeleteCache.get()}, Touching ${f.name}"} }
        } catch(e: Exception) {
            logger.warn(e) {
                "Failed to touch file $f - ${e.message}"
            }
        }
    }
}

/**
 * An entry point that takes
 * (1) a CoreTACProgram in binary file format
 * (2) an out name, optionally, otherwise will be "out"
 *
 * and generates two files: out.tac and out.html corresponding to the input binary.
 *
 */
fun main(args: Array<String>) {
    val f = args.get(0)
    val p = ObjectSerialization.readObject<CoreTACProgram>(f)
    p.writeToOutTAC(args.getOrElse(1) { "out" })
    System.exit(0)
}
