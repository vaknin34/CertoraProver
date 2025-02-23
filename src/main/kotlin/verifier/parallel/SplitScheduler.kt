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

package verifier.parallel

import datastructures.stdcollections.*
import kotlinx.coroutines.*
import kotlinx.coroutines.sync.*
import log.*
import parallel.ParallelPool
import parallel.coroutines.io
import verifier.splits.SplitTree
import verifier.splits.splitComparator
import kotlin.random.Random

private val logger = Logger(LoggerTypes.TACSPLITTER)

/**
 * Utility class for scheduling work items. Its main interface is [runParallel] which runs a given list of items
 * asynchronously and returns their results. Internally, it maintains a [queue] of all work items from all calls to
 * [runParallel] and employs a custom heuristic to schedule them to the underlying thread pool.
 */
class SplitScheduler(
    /** do round-robin with this list of heuristics */
    val heuristic: Array<SchedulingHeuristic> = arrayOf(SchedulingHeuristic.ByPriority),
    /** the next heuristic in the round-robin scheme */
    private var nextHeuristic: Int = 0,
) {
    /** retrieves the next heuristic to be used and shifts the round-robin counter to the next */
    private fun curHeuristic() = heuristic[nextHeuristic].also {
        nextHeuristic = (nextHeuristic + 1) % heuristic.size
    }

    enum class SchedulingHeuristic {
        /** order by depth, and FIFO within a depth */
        ByDepthFIFO,
        /** order by depth, and random within a depth */
        ByDepthRandom,
        ByPriority,
        /** just do a FIFO queue */
        FIFO,
        /** select randomly */
        Random,
    }
    /** The [WorkInfo] class holds the data used for ordering the [Work] objects in the [queue]. */
    data class WorkInfo(
        val split: SplitTree.Node,
    ): Comparable<WorkInfo> {
        override fun compareTo(other: WorkInfo): Int = comparator.compare(this, other)
        companion object {
            /**
             * Define a lexicographic comparison of multiple criteria:
             * - prefer splittable over not splittable
             * - prefer deeper splits
             * - prefer smaller addresses (reverse lexicographically, but ignore last bit)
             * - if splits are siblings, prefer the one with a higher score
             *
             * NB: one might be tempted to move the last criterion up and avoid the little dance of ignoring the last
             * bit in the address comparison. This breaks transitivity, though (see CERT-5970). We thus make the two use
             * entirely different data.
             */
            private val comparator = listOf(
                // prefer splittable
                compareBy { w: WorkInfo -> !w.split.probablySplittable },
                Comparator { w1 : WorkInfo, w2 : WorkInfo ->
                    splitComparator.compare(w1.split, w2.split)
                }
            ).reduce { comp, c -> comp.thenComparing(c) }
        }
    }
    /**
     * Represents a work item, consisting of a trigger signal [start], the deferred [result] with the attached function
     * that is to be run, and an [info] used by the scheduling heuristic.
     */
    data class Work<T>(
        val start: CompletableDeferred<Unit>,
        val result: Deferred<T>,
        val info: WorkInfo,
    )
    /** The queue of work items */
    private val queue = mutableListOf<Work<*>>()
    private val mutex = Mutex()
    /** The full list of all jobs */
    private val allJobs = mutableListOf<Work<*>>()
    /** Whether this scheduler is still active */
    private var active = true

    /**
     * Utility function to sort the [queue] according to the current heuristic. It ultimately uses [List.sort], which
     * claims to be quasi-linear for almost sorted inputs. Most likely, using this repeatedly is slower than using a
     * heap-based priority queue, but it should be good enough. For various reasons, available implementations (e.g.
     * [PriorityQueue]) do not support the operations necessary for [SchedulingHeuristic.Random] or
     * [SchedulingHeuristic.ByDepthRandom] in an efficient way, but would rather require a linear search. We thus go
     * for the much simpler implementation.
     */
    private fun MutableList<Work<*>>.sort(h: SchedulingHeuristic) = when (h) {
        SchedulingHeuristic.ByDepthFIFO,
        SchedulingHeuristic.ByDepthRandom -> sortBy { it.info.split.depth }
        SchedulingHeuristic.ByPriority -> sortBy { it.info }
        SchedulingHeuristic.FIFO -> Unit
        SchedulingHeuristic.Random -> Unit
    }

    /**
     * Remove and return the next work item from the [queue] according to the current heuristic.
     */
    private suspend fun triggerNext() = mutex.withLock() {
        if (queue.isNotEmpty()) {
            val h = curHeuristic()
            queue.sort(h)
            when (h) {
                // remove first according to sorting order
                SchedulingHeuristic.ByDepthFIFO -> queue.removeFirst()

                SchedulingHeuristic.ByDepthRandom -> {
                    // remove random from first group according to sorting order
                    val firstDepth = queue.first().info.split.depth
                    val firstOfHigherDepth = queue.indexOfFirst { it.info.split.depth != firstDepth }
                    queue.removeAt(Random.nextInt(firstOfHigherDepth))
                }

                SchedulingHeuristic.ByPriority -> queue.removeFirst()

                // just remove the first
                SchedulingHeuristic.FIFO -> queue.removeFirst()

                // remove random element
                SchedulingHeuristic.Random -> queue.removeAt(Random.nextInt(queue.size))
            }.also {
                logger.trace { "triggering [${it.result.job}]" }
            }.start.complete(Unit)
        }
    }

    /**
     * Runs [transform] on all work [items] asynchronously, scheduling it together with other work items from other
     * calls to this function. The [info] function is used to retrieve the work item information necessary for the
     * scheduling heuristic.
     */
    suspend fun <T> runParallel(items: Iterable<T>, transform: suspend (T) -> Unit, info: (T) -> WorkInfo) = coroutineScope {
        val work = mutex.withLock() {
            if (!active) {
                logger.trace { "[${this.coroutineContext.job}] skip runParallel" }
                return@coroutineScope
            }
            logger.trace { "[${this.coroutineContext.job}] starting runParallel" }
            // Create work items from [items]
            items.map {
                val start = CompletableDeferred<Unit>()
                Work(
                    start,
                    async {
                        logger.trace { "[${this.coroutineContext.job}] waiting to be triggered..." }
                        start.await()
                        if (active) {
                            logger.trace { "[${this.coroutineContext.job}] triggering the next..." }
                            // Now trigger the next one
                            triggerNext()
                            logger.trace { "[${this.coroutineContext.job}] yay, let's go..." }

                            ParallelPool.inherit(ParallelPool.SpawnPolicy.GLOBAL) { pool ->
                                pool.io {
                                    transform(it)
                                }
                            }
                        }
                        logger.trace { "[${this.coroutineContext.job}] done..." }
                    },
                    info(it)
                )
            }.onEach {
                logger.trace { "[${this.coroutineContext.job}] scheduling [${it.result.job}]..." }
            }.also {
                // Add all work items to the [queue]
                allJobs.addAll(it)
                queue.addAll(it)
            }
        }
        // Trigger the first job, subsequent jobs are triggered once the first one has started.
        triggerNext()
        // Wait for all work items and return their results.
        logger.trace {
            val desc = work.joinToString(", ") { "[${it.result.job}]" }
            "[${this.coroutineContext.job}] waits for ${desc}"
        }
        //dotDump.dump()
        work.map { it.result }.awaitAll()
        logger.trace { "[${this.coroutineContext.job}] returning!" }
    }

    /**
     * Shutdown this scheduler. Sets [active] to make sure that no further jobs are scheduled, and
     * cancels all jobs that are already scheduled.
     */
    suspend fun shutdown() {
        logger.info { "Abort & shutdown" }
        mutex.withLock() {
            active = false
            allJobs.forEach { it.result.cancel() }
        }
    }
}
