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

package rules

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import parallel.ParallelPool
import parallel.pcompute
import rules.dpgraph.*
import java.util.concurrent.atomic.AtomicInteger

typealias TestDPResult = DPResult<DPGraphTest.TaskResult, DPGraphTest.TaskResult, Nothing>
fun testDpResultGenerator(result: DPGraphTest.TaskResult, typ: DPResult.ComputationalType): TestDPResult =
    DPResult.Success(result, typ)

class DPGraphTest {

    companion object {
        val ordinal = TestExecutionIntOrdinalFactory()
    }

    @JvmInline
    value class TestExecutionIntOrdinal(override val ord: Int) : ExecutionOrdinal<Int> {
        override fun compareTo(other: ExecutionOrdinal<Int>): Int = ord.compareTo(other.ord)
    }

    class TestExecutionIntOrdinalFactory : ExecutionOrdinalFactory<Int> {
        override val bottom = TestExecutionIntOrdinal(0)
        private val taskNum = AtomicInteger(0)
        override fun next() : TestExecutionIntOrdinal = TestExecutionIntOrdinal(taskNum.addAndGet(1))
    }

    /**
     * [ordinal] should reflect the order of execution in the graph in the following sense:
     * If N and M are nodes in the graph, the task was executed on N before M, n is the [ordinal] of the result
     * associated to N and m is the [ordinal] of the result associated to M, then n < m.
     */
    data class TaskResult(val result: Int, val ordinal: TestExecutionIntOrdinal, val deduced: Boolean)

    /**
     * This class is not a data class to have equals by reference (and allow multiple nodes with the same payload)
     */
    class TestNode(override val payload: Int) : DPNode<Int, TaskResult, TaskResult, Nothing, TestNode> {

        override fun concludeResultFromPredsOrNull(predNodesToResults: Map<TestNode, TestDPResult>): TaskResult? =
            predNodesToResults.values
                .map{ it.result }
                .fold(payload) { a, b -> a + b.result }.takeIf { it > 0 }?.let {
                TaskResult(it, ordinal.next(), true)
            }
    }

    object LinearDependencies : DependenciesGenerator<Int, TaskResult, TaskResult, Nothing, TestNode> {

        /**
         * payloads[n] depends on payloads[n+1], last one has no deps
         */
        override fun DependenciesGenerator<Int, TaskResult, TaskResult, Nothing, TestNode>
                .doGenerate(payloads: List<Int>): DPGraph<Int, TaskResult, TaskResult, Nothing, TestNode> =
            DPGraph(
                payloads
                    .map { TestNode(it) }
                    .let { nodes ->
                        nodes.mapIndexed { idx, node ->
                            node to if (idx == payloads.size - 1) {
                                setOf()
                            } else {
                                setOf(nodes[idx + 1])
                            }
                        }.toMap()
                    },
                ::testDpResultGenerator
            )
    }

    object CyclicDependencies : DependenciesGenerator<Int, TaskResult, TaskResult, Nothing, TestNode> {

        /**
         * payloads[n] depends on payloads[n+1], last one depends on payloads[0]
         */
        override fun DependenciesGenerator<Int, TaskResult, TaskResult, Nothing, TestNode>
                .doGenerate(payloads: List<Int>): DPGraph<Int, TaskResult, TaskResult, Nothing, TestNode> =
            DPGraph(
                payloads
                    .map { TestNode(it) }
                    .let { nodes ->
                        nodes.mapIndexed { idx, node ->
                            node to if (idx == payloads.size - 1) {
                                setOf(nodes[0])
                            } else {
                                setOf(nodes[idx + 1])
                            }
                        }.toMap()
                    },
                ::testDpResultGenerator
            )
    }

    object Fibonacci : DependenciesGenerator<Int, TaskResult, TaskResult, Nothing, TestNode> {

        /**
         * payloads[0] has no dependencies, payloads[1] depends on payloads[0], payloads[n] depends on payloads[n-1] and
         * payloads[n-2] for n >= 2.
         */
        override fun DependenciesGenerator<Int, TaskResult, TaskResult, Nothing, TestNode>
                .doGenerate(payloads: List<Int>): DPGraph<Int, TaskResult, TaskResult, Nothing, TestNode> {

            val nodes = payloads.map { TestNode(it) }
            val n = nodes.size
            if (n == 0) {
                DPGraph(mapOf<TestNode, Set<TestNode>>(), ::testDpResultGenerator)
            }
            if (n == 1) {
                return DPGraph(
                    mapOf(nodes[0] to setOf()), ::testDpResultGenerator
                )
            }
            return DPGraph(
                mutableMapOf<TestNode, Set<TestNode>>().also {
                    it[nodes[0]] = setOf()
                    it[nodes[1]] = setOf(nodes[0])
                    for (i in 2..nodes.lastIndex) {
                        it[nodes[i]] = setOf(nodes[i - 1], nodes[i - 2])
                    }
                },
                ::testDpResultGenerator
            )
        }
    }

    object MultipleOrders : DependenciesGenerator<Int, TaskResult, TaskResult, Nothing, TestNode> {

        /**
         *             ↗ payloads[2] ↘             ↗ payloads[5] ↘
         * payloads[0]                 payloads[3]                 payloads[6] . . .
         *             ↘ payloads[1] ↗             ↘ payloads[4] ↗
         */
        override fun DependenciesGenerator<Int, TaskResult, TaskResult, Nothing, TestNode>
                .doGenerate(payloads: List<Int>): DPGraph<Int, TaskResult, TaskResult, Nothing, TestNode> {
            val deps = mutableMapOf<TestNode, Set<TestNode>>()
            val nodes = payloads.map { TestNode(it) }
            for (i in 0..nodes.lastIndex) {
                when (i % 3) {
                    0 -> {
                        deps[nodes[i]] = if (i + 2 <= nodes.lastIndex) {
                            setOf(nodes[i + 1], nodes[i + 2])
                        } else if (i + 1 <= nodes.lastIndex) {
                            setOf(nodes[i + 1])
                        } else {
                            setOf()
                        }
                    }
                    1 -> {
                        deps[nodes[i]] = if (i + 2 <= nodes.lastIndex) {
                            setOf(nodes[i + 2])
                        } else {
                            setOf()
                        }
                    }
                    2 -> {
                        deps[nodes[i]] = if (i + 1 <= nodes.lastIndex) {
                            setOf(nodes[i + 1])
                        } else {
                            setOf()
                        }
                    }
                }
            }
            return DPGraph(deps, ::testDpResultGenerator)
        }

    }

    object XShaped : DependenciesGenerator<Int, TaskResult, TaskResult, Nothing, TestNode> {

        /**
         * When [payloads.size] == 4*k + 1 for k > 0, the graph is generated in the following way:
         * Make a partition
         *     p_i = payloads[ik..(i+1)k - 1] for 0 <= i <= 3,
         *     p_5 = payloads[4k]
         * and generate the graph
         *    p_0[0] → . . . → p_0[k - 1] ↘        ↗ p_2[0] → . . . → p_2[k - 1]
         *                                  p_4[0]
         *    p_1[0] → . . . → p_1[k - 1] ↗        ↘ p_3[0] → . . . → p_3[k - 1]
         *
         * When [payloads.size] doesn't satisfy the requirement above, the generated graph is empty.
         */
        override fun DependenciesGenerator<Int, TaskResult, TaskResult, Nothing, TestNode>
                .doGenerate(payloads: List<Int>): DPGraph<Int, TaskResult, TaskResult, Nothing, TestNode> {
            if (payloads.size < 5 || payloads.size % 4 != 1) {
                return DPGraph(emptyMap(), ::testDpResultGenerator)
            }
            val subLists = payloads.map { TestNode(it) }.chunked(payloads.size / 4)
            val map = mutableMapOf<TestNode, Set<TestNode>>().also { map ->
                subLists[0].forEachIndexed { idx, node ->
                    if (idx == subLists[0].lastIndex) {
                        map[node] = setOf(subLists[4][0])
                    } else {
                        map[node] = setOf(subLists[0][idx + 1])
                    }
                }
                subLists[1].forEachIndexed { idx, node ->
                    if (idx == subLists[1].lastIndex) {
                        map[node] = setOf(subLists[4][0])
                    } else {
                        map[node] = setOf(subLists[1][idx + 1])
                    }
                }

                map[subLists[4][0]] = setOf(subLists[2][0], subLists[3][0])

                subLists[2].forEachIndexed { idx, node ->
                    if (idx == subLists[2].lastIndex) {
                        map[node] = setOf()
                    } else {
                        map[node] = setOf(subLists[2][idx + 1])
                    }
                }
                subLists[3].forEachIndexed { idx, node ->
                    if (idx == subLists[3].lastIndex) {
                        map[node] = setOf()
                    } else {
                        map[node] = setOf(subLists[3][idx + 1])
                    }
                }

            }
            return DPGraph(map, ::testDpResultGenerator)
        }

    }

    val positiveIntPayload = (10 downTo 1).toList()
    val negativeIntPayload = (-1 downTo -10).toList()
    val task: (Int) -> TaskResult = { TaskResult(it, ordinal.next(), false) }
    val reduce: (List<TestDPResult>) -> List<TaskResult> = { it.map{ it.result }.sortedBy { it.ordinal } }

    /**
     * This function should be used when the monotonicity of the results in [l] reflects the wanted execution order.
     */
    fun checkLinearOrder(l: List<TaskResult>): Boolean =
        (0 until l.lastIndex).toList().all { i ->
            l[i].result <= l[i + 1].result
        }

    @Test
    fun testLinearDeps() {
        // In each case the results should be monotonic increasing
        val resultPositive = runBlocking {
            LinearDependencies.generate(positiveIntPayload).resultComputation(task, reduce)
        }
        val resultNegative = runBlocking {
            LinearDependencies.generate(negativeIntPayload).resultComputation(task, reduce)
        }
        assertTrue(
            checkLinearOrder(resultPositive),
            "the order of execution of $resultPositive is not a topological order of the graph"
        )
        assertTrue(resultPositive.size == 10, "graph has 10 nodes but got ${resultPositive.size} results")
        assertTrue(resultPositive.all { it.deduced }, "all of the results should be deduced, got $resultPositive")

        assertTrue(
            checkLinearOrder(resultNegative),
            "the order of execution of $resultNegative is not a topological order of the graph"
        )
        assertTrue(resultNegative.size == 10, "graph has 10 nodes but got ${resultNegative.size} results")
        assertTrue(resultNegative.all { !it.deduced }, "none of the results should be deduced, got $resultNegative")
    }

    @Test
    fun testNotDAG() {
        assertThrows(Exception::class.java) {
            CyclicDependencies.generate(positiveIntPayload)
        }
    }

    @Test
    fun testFibonacci() {
        val result = runBlocking {
            Fibonacci.generate(
                mutableListOf<Int>().also {
                    it.add(0)
                    it.add(1)
                    it.addAll(List(19) { 0 })
                }
            ).resultComputation(task, reduce)
        }
        assertTrue(checkLinearOrder(result),
            "the order of execution of $result is not a topological order of the graph")
        assertTrue(result.size == 21, "graph has 21 nodes but got ${result.size} results")
        assertTrue(
            result.withIndex().all { (idx, value) ->
                when (idx) {
                    0 -> value.result == 0
                    1 -> value.result == 1
                    else -> {
                        value.result == result[idx - 1].result + result[idx - 2].result
                    }
                }
            },
            "this graph computation should produce the first 21 terms of the Fibonacci sequence, got ${result.map { it.result }}"
        )
    }

    @Test
    fun testTwoComponents() {
        operator fun DPGraph<Int, TaskResult, TaskResult, Nothing, TestNode>
            .plus(other: DPGraph<Int, TaskResult, TaskResult, Nothing, TestNode>): DPGraph<Int, TaskResult, TaskResult, Nothing, TestNode> =
            DPGraph(
                graph = (this as Map<TestNode, Set<TestNode>>) + (other as Map<TestNode, Set<TestNode>>),
                dpResultGenerator = ::testDpResultGenerator
            )

        // The results should be monotonic increasing for each component separately
        val result = runBlocking {
            (LinearDependencies.generate(positiveIntPayload) + LinearDependencies.generate(negativeIntPayload))
                .resultComputation(task, reduce)
        }
        val (positiveResults, negativeResults) = result.partition { it.result >= 0 }
        assertTrue(
            checkLinearOrder(positiveResults),
            "the order of execution of $result is not a topological order of the graph"
        )
        assertTrue(
            positiveResults.size == 10,
            "component has 10 nodes but got ${positiveResults.size} results"
        )
        assertTrue(positiveResults.all { it.deduced }, "all of the results should be deduced, got $positiveResults")

        assertTrue(
            checkLinearOrder(negativeResults),
            "the order of execution of $result is not a topological order of the graph"
        )
        assertTrue(
            negativeResults.size == 10,
            "component has 10 nodes but got ${negativeResults.size} results"
        )
        assertTrue(negativeResults.all { !it.deduced }, "none of the results should be deduced, got $negativeResults")
    }

    @Test
    fun testMultipleOrders() {
        val result = runBlocking {
            MultipleOrders.generate(negativeIntPayload.reversed()).resultComputation(task, reduce)
        }
        assertTrue(result.size == 10, "graph has 10 nodes but got ${result.size} results")
        assertTrue(
            result.withIndex().all { (idx, res) ->
                when (idx % 3) {
                    2 -> {
                        res.result == -(idx + 1) || res.result == -idx
                    }
                    0 -> {
                        res.result == -(idx + 1)
                    }
                    1 -> {
                        res.result == -(idx + 1) || res.result == -(idx + 2)
                    }
                    else -> {
                        false
                    }
                }
            },
            "the order of execution of $result is not a topological order of the graph"
        )
        assertTrue(result.all { !it.deduced }, "none of the results should be deduced, got $result")
    }

    @Test
    fun testXShaped() {
        /**
         * Test for the graph
         *   0 →  0 ↘   ↗ 1 → 0
         *            0
         *   0 → -1 ↗   ↘ 0 → 0
         */
        val result = runBlocking {
            XShaped.generate(listOf(0, 0, 0, -1, 1, 0, 0, 0, 0)).resultComputation(task, reduce)
        }
        assertTrue(result.size == 9, "graph has 9 nodes but got ${result.size} results")
        assertTrue(result.subList(0, 4).count { it.deduced } == 1,
            "only one of the results ${result.subList(0, 4)} should be concluded from preds")
        assertTrue(result[4].deduced, "middle node in the graph should be concluded, got ${result[4]}")
        assertTrue(result.subList(5, result.size).count { it.deduced } == 2,
            "only two of the results ${result.subList(5, result.size)} should be concluded from preds")
    }
}
