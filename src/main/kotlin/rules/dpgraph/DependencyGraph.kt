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

package rules.dpgraph

import kotlinx.coroutines.coroutineScope
import log.Logger
import log.LoggerTypes
import parallel.coroutines.parallelMapOrdered
import java.util.concurrent.ConcurrentHashMap

private val logger = Logger(LoggerTypes.DEPS_GRAPH)


/**
 * A graph of vertices of type [N] with payload [T] that can be mapped to a [DPResult] of type [R].
 * The graph is used for parallel computing of a task on the underlying set of payloads according to dependencies, while
 * concluding results along the way if possible.
 * The graph is represented by the map [graph] which maps each node to its direct predecessors.
 */
class DPGraph<T, R, S: R, E: R, N: DPNode<T, R, S, E, N>>(
    private val graph: Map<N, Set<N>>,
    val dpResultGenerator: (R, DPResult.ComputationalType) -> DPResult<R, S, E>
    ) : Map<N, Set<N>> by graph {

    /**
     * Given a result for some predecessors of [node], tries to conclude a result for [node].
     * [results] may only contain results of predecessors of [node], while there may be predecessors of [node] that do
     * not occur in [results] (applies to cases where the result can be concluded from a subset of predecessors).
     */
    fun concludeResForNode(node: N, results: Map<N, DPResult<R, S, E>>): R? {
        val nodePreds: Set<N> = graph[node] ?: throw IllegalArgumentException("input $node is not a node in the graph")
        if(results.keys.any { it !in nodePreds }) {
            throw IllegalArgumentException("the given set ${results.keys} is not a set of predecessors of $node")
        }
        return node.concludeResultFromPredsOrNull(results)
    }

    /**
     * Validates that the nodes v such that ord(v) > [bottom] are topologically sorted by [ord]. The order is inverted:
     * if (s, t) is an edge and ord(s), ord(t) > [bottom] then ord(t) < ord(s)
     */
    fun <O : Comparable<O>> validatePartialTopologicalOrder(
        bottom: ExecutionOrdinal<O>,
        ord: (N) -> ExecutionOrdinal<O>
    ) =
        graph.all { (s, ts) ->
            val ordS = ord(s)
            ts.all { t ->
                val ordT = ord(t)
                // Either [s] has not been scheduled, or [s] has been scheduled after [t]
                ordS == bottom || ordS > ordT
            }
        }

    /**
     * Gets the result of [task] on [graph] nodes' payloads with respect to the given
     * dependencies and then reduces the result using [reduce]
     */
    suspend fun <V> resultComputation(
        task: suspend (T) -> R,
        reduce: (List<DPResult<R, S, E>>) -> V,
        loggerMsg: ((T) -> String)? = null
    ): V =
        DPGraphTraversal(this, task, reduce, loggerMsg).traverseAll()
}


/**
 * Carries the computation described in [DPGraph]. Used only in [DPGraph.resultComputation]
 * @param T type of graph nodes' payload
 * @param R result type of [task]
 * @param N type of graph node
 * @param V type of the reduced result
 */
class DPGraphTraversal<T, R, S: R, E: R, N: DPNode<T, R, S, E, N>, V>(
    val deps: DPGraph<T, R, S, E, N>,
    val task: suspend (T) -> R,
    val reduce: (List<DPResult<R, S, E>>) -> V,
    private val loggerMsg: ((T) -> String)? = null
) {

    enum class TaskStatus {
        UNSCHEDULED,
        IN_PROCESS,
        DONE
    }

    /**
     * Used to assign an ordinal to a computation finished on a task. The computation might be either [task] or
     * [DPGraph.concludeResForNode].
     * The ordinal reflects the order of task execution.
     */
    private val taskOrdinalFactory: ExecutionOrdinalFactory<Int> = ExecutionIntOrdinalFactory()

    /**
     * Maps each graph node to execution ordinal of the computation ([task] or [DPGraph.concludeResForNode]) associated
     * with that node.
     */
    private val executionOrder = ConcurrentHashMap<N, ExecutionOrdinal<Int>>().also { map ->
        deps.keys.forEach { map[it] = taskOrdinalFactory.bottom }
    }

    /**
     * Maps each graph node to the status of the computation ([task] or [DPGraph.concludeResForNode]) associated with
     * that node.
     */
    private val status = ConcurrentHashMap<N, TaskStatus>().also { map ->
        // Initially, marking all DPGraphs' nodes as UNSCHEDULED
        deps.keys.forEach { map[it] = TaskStatus.UNSCHEDULED }
    }

    /**
     * Maps each key to the result of [task] or the result of the conclusion.
     */
    private val results = ConcurrentHashMap<N, DPResult<R, S, E>>()

    private fun R.liftResult(computationalTyp: DPResult.ComputationalType): DPResult<R, S, E> =
        deps.dpResultGenerator(this, computationalTyp)

    /**
     * Reduces the result, used after the traversal is finished
     */
    private fun getReducedResults() = reduce(results.entries.map { (_, v) -> v })

    /**
     * The node [n] should be scheduled if the computation is done for all of its dependencies.
     */
    private fun shouldSchedule(n: N): Boolean =
        deps[n]?.all { v ->
            status[v] == TaskStatus.DONE
        } ?: throw IllegalArgumentException("expected $n to be a node in $deps")


    /**
     * Computes the result of [task] on [root] and then computes [recursiveTraversalFromRoot] in parallel for every
     * node which depends on [root] and the result of [shouldSchedule] on it returns true.
     */
    private suspend fun recursiveTraversalFromRoot(root: N): Unit = coroutineScope {
        val firstSchedulingForRoot = status.replace(root, TaskStatus.UNSCHEDULED, TaskStatus.IN_PROCESS)

        if (!firstSchedulingForRoot) {
            return@coroutineScope
        }

        if (loggerMsg != null) {
            logger.debug { "starting on: ${loggerMsg.invoke(root.payload)}" }
        }

        // Concludes the result of [task] without executing it if possible
        val depsResults = deps[root]?.associateWith {
            results[it] ?: throw IllegalStateException(
                "expected the node $it to have a result at this stage"
            )
        } ?: throw IllegalStateException("expected the node $root to have dependencies set")

        results.putIfAbsent(
            root,
            deps.concludeResForNode(root, depsResults)?.liftResult(DPResult.ComputationalType.CONCLUDED)
                ?: task(root.payload).liftResult(DPResult.ComputationalType.COMPUTED)
        )?.also {
            // avoids computing a result twice
            throw IllegalStateException("tried to compute a result twice for $root")
        }

        executionOrder.replace(root, taskOrdinalFactory.bottom, taskOrdinalFactory.next()).also { replaced ->
            // avoids setting an execution ordinal twice
            if (!replaced) {
                throw IllegalStateException("tried to set an execution ordinal for already executed task on $root")
            }
        }

        status[root] = TaskStatus.DONE

        // executing the traversal on all the nodes that are ready to schedule due to the completion of the computation
        // on [root]
        val readyForExecution = deps.entries
            .filter { (node, depNodes) -> root in depNodes && shouldSchedule(node) }

        if (readyForExecution.isNotEmpty()) {
            readyForExecution.parallelMapOrdered { _, (node, _) -> recursiveTraversalFromRoot(node) }
        }
    }

    /**
     * Traverses the graph and executes [task] on each node it reaches and the reduces the
     * results to a single result. The traversal starts from the nodes which are ready to schedule and is done in
     * parallel.
     */
    suspend fun traverseAll(): V = coroutineScope {
        deps.entries
            .filter { (node, _) -> shouldSchedule(node) }
            .parallelMapOrdered { _, (node, _) -> recursiveTraversalFromRoot(node) }

        getReducedResults().also { _ ->
            if (!deps.validatePartialTopologicalOrder(taskOrdinalFactory.bottom) { t ->
                    executionOrder[t] ?: throw IllegalStateException("expected task $t to have an execution ordinal")
            }) {
                throw IllegalStateException("task execution is not topologically sorted")
            }
            logger.debug { "finished graph traversal" }
        }
    }
}
