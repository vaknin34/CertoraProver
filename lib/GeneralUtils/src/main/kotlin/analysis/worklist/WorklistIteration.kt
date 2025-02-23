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

package analysis.worklist

import com.certora.collect.*
import datastructures.ArrayHashSet
import datastructures.stdcollections.*

sealed class StepResult<out T, out U, out R> {
    data class Ok<T, U>(val next: Iterable<T>, val result: Iterable<U>) : StepResult<T, U, Nothing>()
    data class StopWith<R>(val ret: R) : StepResult<Nothing, Nothing, R>()
}

/**
 * An abstract implementation of a worklist. Implementers should override [process], which
 * which processes a single work item of type [T] and produces a [StepResult]. The [StepResult]
 * may either generate 0 or more work items (of type [T]) and zero or more intermediate results (of type [U])
 * by returning [StepResult.Ok], or it may halt the iteration immediately with a final result [StepResult.StopWith]
 *
 * The worklist is processed in batches. Beginning with the first set of work items submitted via [submit],
 * each pending item is processed (via the [step]/[process]) functions before any additional items generated
 * by an [StepResult.Ok] are processed. Thus, it is generally safe to have a work item return itself, provided
 * you know that progress made on other work items will cause these "self-loops" to cease.
 *
 * Assuming no [StepResult.StopWith] results are generate, all intermediate results of type [U] are collected
 * into a final return of type [R] via the [reduce] operation.
 */
abstract class WorklistIteration<@Treapable T, U, R> {
    open val scheduler : IWorklistScheduler<T> get() = ChaoticWorklistIteration

    open fun submit(workItems: Iterable<T>) : R {
        var worklist = workItems.toTreapSet()
        val results = mutableListOf<U>()

        while (worklist.isNotEmpty()) {
            val sched = worklist
            var next = treapSetOf<T>()

            worklist.forEach { l ->
                if (scheduler.shouldSchedule(l, { sched })) {
                    when (val res = this.step(l)) {
                        is StepResult.StopWith -> return res.ret
                        is StepResult.Ok -> {
                            results += res.result
                            next += res.next
                        }
                        else -> {
                            // Intentionally left blank, do nothing
                        }
                    }
                    // We remove items from worklist, rather than building up `next` as we go, because it's common
                    // to skip lots of (most) workitems due to the scheduler.  In those cases, it's much faster
                    // to just remove a couple of workitems than to build up a new, nearly-identical, set.  In the
                    // cases where we do most of the work, the cost of removing the items individually is dwarfed
                    // by the cost of the work itself.
                    worklist -= l
                }
            }
            worklist += next

            if (worklist.isNotEmpty()) {
                nextRound(worklist)
            }
        }
        return this.reduce(results)
    }

    protected open fun step(it: T): StepResult<T, U, R>? = this.process(it)

    protected abstract fun process(it: T): StepResult<T, U, R>

    protected abstract fun reduce(results: List<U>): R

    fun cont(k: Iterable<T>) : StepResult<T, U, R> = StepResult.Ok(k, listOf())
    fun cont(k: T) : StepResult<T, U, R> = StepResult.Ok(listOf(k), listOf())
    fun result(k: Iterable<U>) : StepResult<T, U, R> = StepResult.Ok(listOf(), k)
    fun result(k: U) : StepResult<T, U, R> = StepResult.Ok(listOf(), listOf(k))

    fun halt(t: R) : StepResult<T, U, R> = StepResult.StopWith(t)

    /** Called between each pass through the worklist.  Override this to update state based on remaining work. */
    open fun nextRound(worklist: Iterable<T>) = Unit
}

/**
 * A stateful worklist that has some internal mutable state that is changed during processing.
 * Thus submit may only be called at most once
 */
abstract class StatefulWorklistIteration<@Treapable T, U, R> : WorklistIteration<T, U, R>() {
    private var run = false

    override fun submit(workItems: Iterable<T>): R {
        if(run) {
            throw IllegalStateException("Cannot run this analysis more than once")
        }
        run = true
        return super.submit(workItems)
    }
}

/**
 * A stateful worklist iteration that tracks visited work items and ensures that [process] is called
 * for any work item exactly once (any future "processing" of a previously processed [T] produces an empty result)
 */
abstract class VisitingWorklistIteration<@Treapable T, U, R> : StatefulWorklistIteration<T, U, R>() {
    private val visited = ArrayHashSet<T>()

    override fun step(it: T): StepResult<T, U, R>? {
        if (!visited.add(it)) {
            return null
        }
        return this.process(it)
    }
}
