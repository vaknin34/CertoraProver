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

package parallel.coroutines

import kotlinx.coroutines.*
import parallel.ParallelPool
import utils.*
import kotlin.coroutines.*
import kotlin.time.Duration

/**
 * Launch a coroutine in the scope of the `main` function.  This coroutine will run in the background, and will need
 * to complete before the process exits. [launchBackground] can only be called while [establishMainCoroutineScope] is
 * active.
 *
 * [name] is a human-readable name for the coroutine, used for debugging.
 */
fun launchBackground(
    name: String,
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> Unit
): Job = mainCoroutineScope.launch(context + CoroutineName(name)) { block() }

/**
    Like [launchBackground], but does not require a main coroutine scope to be active.  In that case we'll just run
    the coroutine directly on this thread.  This is useful for code that may run inside of unit tests.
 */
fun launchMaybeBackground(
    name: String,
    context: CoroutineContext = EmptyCoroutineContext,
    block: suspend CoroutineScope.() -> Unit
): Job = if (mainCoroutineScope.isActive) {
    launchBackground(name, context, block)
} else {
    // In tests, we may not have a main coroutine scope.  In that case, we can just run the coroutine directly on this
    // thread.
    onThisThread {
        withContext(context + CoroutineName(name)) {
            block()
        }
    }
    // We have to return a Job, but the coroutine is already complete.  So we create a new Job and immediately complete 
    // it.
    Job().also { it.complete() }
}

/**
 * Called by `main`.  Top-level coroutines can be started while this function is active (for the duration of [block]'s
 * execution).  [block] itself is run as a coroutine, using a new [ParallelPool] as the dispatcher.
 *
 * After [block] has finished, this function waits for all background coroutines to complete, with an optional timeout
 * given by [exitTimeout].  If the timeout expires, we write the currently running background coroutines to the log.
 */
fun establishMainCoroutineScope(exitTimeout: Duration = Duration.INFINITE, block: suspend (CoroutineScope) -> Unit) {
    mainCoroutineScope.run(defaultTopLevelCoroutineDispatcher, exitTimeout, block)
}

/**
 * The default coroutine dispatcher to use for [TopLevelCoroutineScope].  Since [TopLevelCoroutineScope] is typically
 * used to establish the top-level scope/context for all coroutines started in the process, this will be the default
 * dispatcher for all such coroutines.
 *
 * We use the same pool as ParallelPool, to avoid spinning up yet another thread pool.
 */
val defaultTopLevelCoroutineDispatcher = ParallelPool.globalPool.workerThreadPool.asCoroutineDispatcher()

/**
 * The scope representing the duration of the `main` function.
 */
private val mainCoroutineScope = BackgroundCoroutineScope()

/**
 * A CoroutineScope that can be "published" before it is active, and which does not establish a dispatcher on the thread
 * that starts it.  This allows initialization of a global property with a [BackgroundCoroutineScope], and later (e.g., in
 * `main`) activation of the scope with the proper context.  Unlike [runBlocking], [BackgroundCoroutineScope] does not
 * expose an event loop on the thread that activates the scope, so there is no danger of accidentally running our
 * supposedly-parallel coroutines interleaved on the process' main thread.
 */
internal class BackgroundCoroutineScope : CoroutineScope {

    /**
     * The CoroutineContext for all coroutines launched under this scope.  This is only non-null while [run] is
     * executing.
     */
    private var runningContext: CoroutineContext? = null

    val isActive get() = runningContext != null

    override val coroutineContext get() = runningContext ?: error("Top-level coroutine scope not running")

    /**
     * Activates this scope for the duration of [block].  Runs [block] with a new ParallelPool as the dispatcher.
     * While `block` is running, this scope is available for other code's use, e.g. via
     * `publishedScope.launch { <coroutine> }`. The launched coroutine will have the context passed to [run] (for
     * example, the dispatcher)
     *
     * When [block] exits, [run] waits for the completion of all background coroutines launched in this scope.  If any
     * of them has failed, then [run] rethrows the exception.
     */
    @OptIn(kotlinx.coroutines.ExperimentalCoroutinesApi::class)
    @Suppress("TooGenericExceptionCaught")
    fun run(
        context: CoroutineContext = defaultTopLevelCoroutineDispatcher,
        exitTimeout: Duration = Duration.INFINITE,
        block: suspend (CoroutineScope) -> Unit
    ) {
        check(runningContext == null) { "Top-level coroutine scope already running" }

        // This is the top-level Job encompassing all coroutines started in this scope.  This job will be marked
        // complete when [block] has finished, and all child jobs have completed.
        val job = Job()

        // Jobs don't track the exceptions that caused them to fail.  So we will track this ourselves, using a Deferred
        // and a custom exception handler.
        val deferredResult = CompletableDeferred<Unit>()
        val eh = CoroutineExceptionHandler { _, throwable ->
            deferredResult.completeExceptionally(throwable)
        }

        // Now we're ready to build the CoroutineContext for this scope.  It's the passed-in context (dispatcher, etc.)
        // plus our job and exception handler.  Once this is assigned to [runningContext], the scope is active and ready
        // to accept child jobs.
        runningContext = context + job + eh
        val pool = ParallelPool()
        try {
            // Now we run the block, wait for completion, and deal with exceptions.
            @Suppress("ForbiddenMethodCall")
            runBlocking(pool.workerThreadPool.asCoroutineDispatcher()) {
                try {
                    block(this)

                    // Move the parent job to the "completing" state.  Once all children are completed, the parent will be
                    // completed.
                    job.complete()
                } catch (e: Throwable) {
                    // If [block] fails, cancel any pending child jobs, and remember this exception for later.
                    job.completeExceptionally(e)
                    deferredResult.completeExceptionally(e)
                }

                // Block until all child jobs have completed.
                try {
                    withTimeout(exitTimeout) { job.join() }
                } catch (_: TimeoutCancellationException) {
                    InjectedDependencies().alwaysLogError(
                        "Timed out waiting for background tasks:\n" + job.children.joinToString("\n").prependIndent("    ")
                    )
                }
            }

            // Mark the deferredResult complete.  If it already completed exceptionally, this has no effect.  If not, this
            // allows us to call getCompleted below.
            deferredResult.complete(Unit)

            // Rethrow any exception that happened.
            deferredResult.getCompleted()

        } finally {
            pool.close()
            runningContext = null
        }
    }
}
