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

package parallel

import datastructures.stdcollections.*
import log.*
import parallel.Scheduler.complete
import kotlin.time.Duration
import kotlinx.coroutines.runBlocking
import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicInteger
import java.util.function.Supplier
import utils.*


private val logger = Logger(GeneralUtilsLoggerTypes.PARALLEL)

object Scheduler {
    fun <T> compute(f: () -> T): Parallel<T> = ComputeJob(f)
    fun <T> compute(cancel: (Throwable) -> T, f: () -> T): Parallel<T> =
        CancellableJob(cancel) { -> ComputeJob(f) }

    fun <T> fork(cancel: (Throwable) -> T, f: Scheduler.() -> Parallel<T>): Parallel<T> =
        CancellableJob(cancel, f)

    fun <T> rpc(timeout: Duration? = null, f: suspend () -> T): Parallel<T> = RPCJob(timeout = timeout, job = f)
    fun <T> io(f: () -> T): Parallel<T> = IOJob(job = f)
    fun <T> fork(f: Scheduler.() -> Parallel<T>): Parallel<T> = BindJob(
        listOf()
    ) { Scheduler.f() }

    fun <T> complete(x: T): Parallel<T> = CompleteJob(x)
    fun done(): Parallel<Unit> = CompleteJob(Unit)

    fun <T> `return`(v: T) = complete(v)
}

class CancellableJob<T>(val cancel: (Throwable) -> T, f: Scheduler.() -> Parallel<T>) : Parallel<T>() {
    override val deps: List<Parallel<*>>
        get() = listOf()

    private val task = Scheduler.f()

    private var errorResult: T? = null

    fun signalError(t: Throwable) {
        errorResult = cancel(t)
    }

    override fun done(): Boolean {
        return errorResult != null || task.done()
    }

    override val result: T
        get() = errorResult ?: task.result

    override fun schedule(ioPool: ExecutorService): List<Parallel<*>> {
        return listOf(task)
    }

}

fun <T> Scheduler.forkOrNull(f: Scheduler.() -> Parallel<T?>?) = BindJob(listOf()) {
    this.f() ?: complete(null)
}

infix fun <T, U> Parallel<T>.with(other: Parallel<U>) = Parallel2(this, other)

data class Parallel2<T, U>(val v1: Parallel<T>, val v2: Parallel<U>) {
    infix fun <V> with(other: Parallel<V>) = Parallel3(v1, v2, other)
    fun <V> bind(f: Scheduler.(T, U) -> Parallel<V>) = v1.parallelBind(v2, f)

    infix fun <V> andThen(f: Scheduler.(T, U) -> Parallel<V>) = bind(f)
    infix fun <V> andThenReturn(f: Scheduler.(T, U) -> V) = bind { a, b ->
        complete(Scheduler.f(a, b))
    }
}

data class Parallel3<T, U, V>(val v1: Parallel<T>, val v2: Parallel<U>, val v3: Parallel<V>) {
    infix fun <W> with(other: Parallel<W>) = Parallel4(v1, v2, v3, other)
    fun <W> bind(f: Scheduler.(T, U, V) -> Parallel<W>) = v1.parallelBind(v2, v3, f)
    infix fun <W> andThen(f: Scheduler.(T, U, V) -> Parallel<W>) = bind(f)
    infix fun <W> andThenReturn(f: Scheduler.(T, U, V) -> W) = bind { a, b, c ->
        complete(Scheduler.f(a, b, c))
    }
}

data class Parallel4<T, U, V, W>(val v1: Parallel<T>, val v2: Parallel<U>, val v3: Parallel<V>, val v4: Parallel<W>) {
    fun <X> bind(f: Scheduler.(T, U, V, W) -> Parallel<X>) =
        BindJob(
            listOf(v1, v2, v3, v4)
        ) {
            Scheduler.f(v1.result, v2.result, v3.result, v4.result)
        }

    infix fun <X> andThen(f: Scheduler.(T, U, V, W) -> Parallel<X>) = bind(f)
    infix fun <X> andThenReturn(f: Scheduler.(T, U, V, W) -> Parallel<X>) = bind { a, b, c, d ->
        complete(Scheduler.f(a, b, c, d))
    }
}

/**
 * An instance of [Parallel] represents a computation that can be run and produce a value of type [V].
 *
 * A parallel computation may have zero or more dependent computations which must be fully evaluated before
 * computation represented by a [Parallel] may be run.
 *
 * One all dependencies have completed, each [Parallel] may be [scheduled][schedule] exactly once. The return of [schedule]
 * does *not* necessarily mean the result is ready; it possible that further work (represented by the return type) must
 * be completed before the [result] is ready.
 *
 * The subclasses of [Parallel] are exposed for packaging purposes but should never be instantiated manually. Similarly,
 * the fields and methods of a [Parallel] should not be manipulated outside of the [ParallelPool] implementation.
 */
sealed class Parallel<out V> {
    /**
     * A list of dependency [Parallel] tasks that must be [done] before this [Parallel] may be [scheduled][schedule].
     *
     * Subclasses of [Parallel] are responsible for feeding the result values of the dependencies directly into the
     * computation represented by this class, hence the `*` bound
     */
    abstract val deps: List<Parallel<*>>

    /**
     * Has this [Parallel] completed and its [result] is ready.
     */
    abstract fun done(): Boolean

    /**
     * The result of this [Parallel]. Accessing this before the Parallel is [done] may crash.
     */
    abstract val result: V

    /**
     * Has this Parallel been scheduled yet? set by [queueSchedule]
     */
    var scheduled: Boolean = false

    /**
     * The main entry point for scheduling. The [ioPool] argument is an executor service provides execution
     * on threads guaranteed to be separate from the threads used to execute compute tasks. In other words, [Parallel]
     * tasks that perform IO should immediately schedule their work to be within a [Runnable] executed on [ioPool] so
     * as to not block parallel progress.
     */
    fun queueSchedule(ioPool: ExecutorService): List<Parallel<*>> {
        scheduled = true
        return schedule(ioPool)
    }

    /**
     * Actually perform the computation represented by this [Parallel]. The result of this [Parallel] work may
     * depend on the completion of one or more tasks returned from this method. It is the responsibility
     * of subclasses to track this dependency and override [done] appropriately.
     */
    abstract fun schedule(ioPool: ExecutorService): List<Parallel<*>>

    /**
     * Return a [Parallel] that depends on the completion of this [Parallel] and [t], and then executes
     * [f]. In other words, the returned parallel will await the (potentially parallel) execution of this and [t]
     * and then run [f], which itself returns a
     * [Parallel].
     *
     * [f] runs in the scope of the [Scheduler] object for convenience.
     */
    fun <R, T> parallelBind(t: Parallel<T>, f: Scheduler.(V, T) -> Parallel<R>): Parallel<R> = BindJob(
        listOf(
            this, t
        )
    ) {
        Scheduler.f(this.result, t.result)
    }

    /**
     * As with the binary case, but schedule the three parallels for parallel execution.
     */
    fun <R, T, U> parallelBind(t: Parallel<T>, u: Parallel<U>, f: Scheduler.(V, T, U) -> Parallel<R>) = BindJob(
        listOf(this, t, u)
    ) {
        Scheduler.f(this.result, t.result, u.result)
    }

    fun <R> bind(f: Scheduler.(V) -> Parallel<R>) = BindJob(listOf(this)) {
        Scheduler.f(this.result)
    }

    fun <R> map(f: (V) -> R) = this.bind {
        complete(f(it))
    }

    /**
     * Can this [Parallel] be scheduled? i.e., has it not already been scheduled and are all of its dependencies completed?
     */
    val runnable get() = !scheduled && this.deps.all { it.done() }
}

/**
 * After the computation represented by [this] completes, run the callback [f]. The resulting [Parallel] object
 * will return the value computed by [this].
 *
 * Note that
 * this internall uses [Parallel.bind], so non-zero time may pass between the completion of [this] and the
 * running of [f].
 *
 * Useful mostly for logging and debugging (with the caveats above)
 */
fun <V> Parallel<V>.andAlso(f: () -> Unit) = this.bind {
    f()
    complete(it)
}

/**
 * After the computation computed by [this] completes, run the callback [f] which accepts the value computed.
 * The parallel object returned by this function will return exactly the value computed by [this].
 *
 * The same caveats w.r.t timing as in the no-arg callback case apply.
 */
fun <V> Parallel<V>.andAlso(f: (V) -> Unit) = this.bind {
    f(it)
    complete(it)
}

/**
 * When [this] parallel completes with a non-null result, transform the result to an [R]? via [f]. If it completes with
 * null, then the Parallel returned by this call will also complete with null.
 */
fun <T, R> Parallel<T?>.maybeMap(f: (T) -> R): Parallel<R?> {
    return this.map {
        it?.let(f)
    }
}

/**
 * Run [this] and the value [t] in parallel, and then invoke [f] with their results. If [f] returns `null`,
 * Then the Parallel returned by this function will complete with null. Otherwise, the non-null parallel returned from
 * [f] will be run to completion.
 */
fun <V, R, T> Parallel<V>.parallelBindCommute(t: Parallel<T>, f: Scheduler.(V, T) -> Parallel<R?>?) = BindJob(
    listOf(this, t)
) {
    Scheduler.f(this.result, t.result) ?: Scheduler.complete(null)
}

/**
 * As in the 2 arg case, but run three computations in parallel
 */
fun <V, R, T, U> Parallel<V>.parallelBindCommute(
    t: Parallel<T>,
    u: Parallel<U>,
    f: Scheduler.(V, T, U) -> Parallel<R?>?
) = BindJob(
    listOf(this, t, u)
) {
    Scheduler.f(this.result, t.result, u.result) ?: Scheduler.complete(null)
}

/**
 * Returns a parallel which first computes the value of [this] and then invokes [f] with the result.
 * If [f] returns null, then the [Parallel] returned by this function will complete with null.
 * Otherwise, the non-null parallel is run to completion.
 */
fun <V, R> Parallel<V>.bindCommute(f: Scheduler.(V) -> Parallel<R?>?) = BindJob(listOf(this)) {
    Scheduler.f(this.result) ?: Scheduler.complete(null)
}

fun <V, R> Parallel<V?>.bindComposed(f: Scheduler.(V) -> Parallel<R?>?) = bind {
    if (it == null) {
        complete(null)
    } else {
        f(it) ?: complete(null)
    }
}

/**
 * Returns a Parallel which first runs [this] to completion. If the resulting value is `null`
 * then the returned Parallel also completes with null. Otherwise [f] is run and the Parallel
 * returned by [f] is run to completion.
 */
fun <T, R> Parallel<T?>.maybeBind(f: (T) -> Parallel<R>): Parallel<R?> {
    return bind {
        if (it == null) {
            complete(null)
        } else {
            f(it)
        }
    }
}

/**
 * Commutes the null monad with the parallel monad (duh)
 */
fun <T> Parallel<T>?.commute(): Parallel<T?> = this ?: complete(null)

/**
 * Given a list of Parallels, return a parallel that computes each element in parallel, and returns a list.
 */
fun <T> Collection<Parallel<T>>.pcompute() = FlattenJob(this.toList())

/**
 * A job that is scheduled in the IO threads, but is expected to cause
 * one CPU to be fully consumed during computation
 */
class RPCJob<T>(private val timeout: Duration?, private val job: suspend () -> T) : Parallel<T>() {
    /*
     * No dependencies
     */
    override val deps: List<Parallel<*>>
        get() = listOf()

    /**
    The [CompletableFuture] which will hold the eventual result of the IO job.
     */
    @Volatile
    lateinit var future: CompletableFuture<T>

    /**
    Simply delegates to the [future]'s [CompletableFuture.get]. Calling this before the parallel is [done] will block
    parallel computation.
     */
    override val result: T
        get() {
            check(future.isDone)
            return future.get()
        }

    /**
     * Do we have a future and is the future reported as done?
     */
    override fun done(): Boolean {
        return this::future.isInitialized && future.isDone
    }

    private var completeFlag = false

    /**
     * Simply initialize the future field with the result of submitting the [job] into the [ioPool].
     */
    override fun schedule(ioPool: ExecutorService): List<Parallel<*>> {
        logger.debug {
            "About to create job in ${Thread.currentThread()}"
        }
        val semaphore = Sem(semaphoreId.incrementAndGet())
        future = CompletableFuture.supplyAsync(Supplier {
            logger.debug {
                "Running blocking io job in thread ${Thread.currentThread()}"
            }
            val r = try {
                @Suppress("ForbiddenMethodCall") // We are running on the io pool, so it's ok to block this thread
                runBlocking {
                    job()
                }
            } finally {
                synchronized(semaphore) {
                    completeFlag = true
                    semaphore.notifyAll()
                }
            }
            r
        }, ioPool)
        synchronized(semaphore) {
            val startTimeMillis = System.currentTimeMillis()
            var hitTimeout = false
            while (!completeFlag && !hitTimeout) {
                if (timeout != null) {
                    val timeRemainingMillis = timeout.inWholeMilliseconds - (System.currentTimeMillis() - startTimeMillis)
                    if (timeRemainingMillis < 0) {
                        hitTimeout = true
                    } else {
                        semaphore.wait(timeRemainingMillis)
                    }
                } else {
                    semaphore.wait()
                }
            }
            if (hitTimeout) {
                future.cancel(true)
            }
        }
        future.get() // NB: this may throw a CancellationException
        return emptyList()
    }
}

private val semaphoreId = AtomicInteger()

@Suppress("PLATFORM_CLASS_MAPPED_TO_KOTLIN") // Need this for the monitor methods, which are otherwise hidden by Kotlin.
class Sem(val id: Int) : java.lang.Object() {
    override fun toString(): String {
        return "SEM$id"
    }
}


/**
 * A job which performs blocking, non-cpu intensive IO
 */
class IOJob<T>(private val job: () -> T) : Parallel<T>() {
    /*
     * No dependencies
     */
    override val deps: List<Parallel<*>>
        get() = listOf()

    /**
    The [CompletableFuture] which will hold the eventual result of the IO job.
     */
    @Volatile
    lateinit var future: CompletableFuture<T>

    /**
    Simply delegates to the [future]'s [CompletableFuture.get]. Calling this before the parallel is [done] will block
    parallel computation.
     */
    override val result: T
        get() {
            check(future.isDone)
            return future.get()
        }

    /**
     * Do we have a future and is the future reported as done?
     */
    override fun done(): Boolean {
        return this::future.isInitialized && future.isDone
    }

    /**
     * Simply initialize the future field with the result of submitting the [job] into the [ioPool].
     */
    override fun schedule(ioPool: ExecutorService): List<Parallel<*>> {
        logger.debug {
            "About to create job in ${Thread.currentThread()}"
        }
        future = CompletableFuture.supplyAsync(Supplier {
            logger.debug {
                "Running blocking io job in thread ${Thread.currentThread()}"
            }
            job()
        }, ioPool)
        ForkJoinPool.managedBlock(object : ForkJoinPool.ManagedBlocker {
            override fun block(): Boolean {
                future.get()
                return true
            }

            override fun isReleasable(): Boolean {
                return future.isDone
            }
        })
        return emptyList()
    }
}

/**
 * Trivial parallel which immediately returns the given [result]
 */
class CompleteJob<T>(override val result: T) : Parallel<T>() {
    override val deps get() = listOf<Parallel<*>>()
    override fun schedule(ioPool: ExecutorService): List<Parallel<T>> = emptyList()
    override fun done(): Boolean {
        return true
    }
}

/**
 * Pure compute job that runs in a parallel work thread and which completes with the result of evaluating [thunk]
 */
class ComputeJob<T>(private val thunk: () -> T) : Parallel<T>() {
    override val deps: List<Parallel<*>>
        get() = emptyList()

    override fun done(): Boolean {
        return this.scheduled
    }

    @Volatile
    private var _result: Either<T, Unit> = Either.Right(Unit)

    override val result: T
        get() = if (_result is Either.Left) {
            (_result as Either.Left).d
        } else {
            throw IllegalStateException("Can't get value from ComputeJob before it is scheduled")
        }

    override fun schedule(ioPool: ExecutorService): List<Parallel<*>> {
        _result = Either.Left(thunk())
        return emptyList()
    }
}

class FlattenJob<T>(private val nested: List<Parallel<T>>) : Parallel<List<T>>() {
    override val deps: List<Parallel<*>>
        get() = nested
    override val result: List<T>
        get() = nested.map { it.result }

    override fun schedule(ioPool: ExecutorService): List<Parallel<*>> {
        return listOf()
    }

    override fun done(): Boolean {
        return this.deps.all { it.done() }
    }
}

/**
 * Once all of [deps] are complete, run [bind] which returns a [Parallel]. The result of this [Parallel] is
 * ultimately the value returned by the nested [parallel] object.
 */
class BindJob<T>(override val deps: List<Parallel<*>>, private val bind: () -> Parallel<T>) : Parallel<T>() {
    /**
     * The [Parallel] returned by [bindCommute]. When it is complete, it becomes the value of this [Parallel]
     */
    @Volatile
    private lateinit var parallel: Parallel<T>

    /**
     * Our result is the child [parallel] [result]
     */
    override val result: T
        get() = parallel.result

    /**
     * We are done when our "child" [parallel] completes
     */
    override fun done(): Boolean {
        return this::parallel.isInitialized && this.parallel.done()
    }

    /**
     * Run the [bindCommute] body and return that [parallel] for further scheduling.
     */
    override fun schedule(ioPool: ExecutorService): List<Parallel<T>> {
        parallel = bind()
        return listOf(parallel)
    }
}

/**
 * For every element in [this] run [f] which should return a parallel computation producing a value of type [U].
 */
fun <T, U> Iterable<T>.forkEvery(f: (T) -> Parallel<U>) =
    this.map {
        Scheduler.fork {
            f(it)
        }
    }

/**
 * For every element in [this], (sequentially) run the function [f]. [f] may return
 * null directly which is commuted to a `Parallel<U?>` that trivial completes with null.
 * Otherwise, the parallel result is used. This list can then be flattened later.
 */
fun <T, U> Iterable<T>.forkEveryOrNull(f: (T) -> Parallel<U?>?) =
    this.map {
        Scheduler.fork {
            f(it) ?: complete(null as U?)
        }
    }

/**
 * If the current parallel holds a boolean, skip the computation in [f] and immediately produce a result
 * as null. Otherwise run the computation in [f] and use it's result
 */
fun <T> Parallel<Boolean>.bindFalseAsNull(f: () -> Parallel<T?>) =
    this.bind {
        if (it) {
            f()
        } else {
            complete(null as T?)
        }
    }
