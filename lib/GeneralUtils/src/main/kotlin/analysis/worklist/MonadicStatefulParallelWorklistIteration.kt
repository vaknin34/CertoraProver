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

package analysis.worklist;

import datastructures.stdcollections.*
import parallel.Parallel
import parallel.ParallelPool
import parallel.Scheduler
import parallel.pcompute

abstract class MonadicStatefulParallelWorklistIteration<T, C, U, R>(private val inheritPool: ParallelPool?) {
    open val scheduler : IWorklistScheduler<T> get() = ChaoticWorklistIteration

    private var run = false

    private var privatePool : ParallelPool? = null

    protected val pool : ParallelPool
        get() = inheritPool ?: privatePool!!

    fun submit(workItems: Iterable<T>): R {
        if(run) {
            throw IllegalStateException("Parallel worklists are considered stateful")
        }
        run = true
        val pool = if(inheritPool != null) {
            inheritPool
        } else {
            val p = ParallelPool()
            privatePool = p
            p
        }
        try {
            var worklist = mutableSetOf<T>()
            worklist.addAll(workItems)
            val results = mutableListOf<U>()
            var nxt = mutableSetOf<T>()
            while (worklist.isNotEmpty()) {
                val res = worklist.mapNotNull { l ->
                    if (!scheduler.shouldSchedule(l, { worklist })) {
                        nxt.add(l)
                        null
                    } else {
                        step(l)
                    }
                }.pcompute().let {
                    pool.run(it)
                }
                for (r in res) {
                    when (r) {
                        is ParallelStepResult.StopWith -> return r.r
                        is ParallelStepResult.Result -> results.addAll(r.res)
                        is ParallelStepResult.FullResult -> {
                            results.addAll(r.res)
                            commitCont(r.cont, nxt, results)
                        }
                        is ParallelStepResult.ContinueWith -> {
                            commitCont(r.cont, nxt, results)
                        }
                    }
                }
                worklist.clear()
                val tmp = worklist
                worklist = nxt
                nxt = tmp
            }
            return this.reduce(results)
        } finally {
            if(privatePool != null) {
                privatePool!!.close()
            }
        }
    }

    private fun commitCont(cont: List<C>, nxt: MutableCollection<T>, results: MutableList<U>) {
        for(c in cont) {
            this.commit(c, nxt, results)
        }
    }

    /**
     * Process an intermediate result [c], modifying some shared state, and producing some new work items
     * (which should be placed in [nxt].
     *
     * Called synchronously, i.e., it is safe to *mutate* shared state within this function.
     */
    protected abstract fun commit(c: C, nxt: MutableCollection<T>, res: MutableCollection<U>)

    /**
     * Process the work item [it] and generate a step result. Called in parallel. It is therefore
     * safe to *read* mutable state but in *generally unsafe* to *mutate* shared state.
     */
    protected open fun step(it: T): Parallel<ParallelStepResult<C, U, R>> = Scheduler.compute { this@MonadicStatefulParallelWorklistIteration.process(it) }

    protected abstract fun reduce(results: List<U>): R
    protected abstract fun process(it: T): ParallelStepResult<C, U, R>

    fun cont(k: Iterable<C>): ParallelStepResult<C, U, R> = ParallelStepResult.ContinueWith(k.toList())

    fun cont(k: C): ParallelStepResult<C, U, R> = ParallelStepResult.ContinueWith(listOf(k))

    fun result(k: Iterable<U>): ParallelStepResult<C, U, R> = ParallelStepResult.Result(k.toList())

    fun result(k: U): ParallelStepResult<C, U, R> = ParallelStepResult.Result(listOf(k))

    fun halt(t: R): ParallelStepResult<C, U, R> = ParallelStepResult.StopWith(t)
}
