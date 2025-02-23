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

package analysis

import algorithms.SCCGraph
import algorithms.postOrder
import algorithms.topologicalOrder
import datastructures.stdcollections.*
import com.certora.collect.*
import utils.*

interface GraphBlockView<Graph, Block, BlockLabel> {
    fun elab(g: Graph, l: BlockLabel): Block
    fun succ(g: Graph, src: Block): Collection<Block>
    fun pred(g: Graph, src: Block): Collection<Block>
    fun blockGraph(g: Graph): Map<BlockLabel, Set<BlockLabel>>
    fun blockId(b: Block): BlockLabel
}

/**
 * Direction of the cfg traversal.
 */
enum class Direction { FORWARD, BACKWARD }

/**
 * BlockDataFlowAnalysis runs the analysis in BFS according to its direction parameter until reaching a fixed point.
 * Usage:
 * Define in the derived class:
 * 1. T - the result of each iteration
 * 2. lattice - appropriate join and equiv functions corresponding to T.
 * 3. fun transform() - compute the result for the current block.
 * 4. an API that returns information from blockIn, blockOut
 * @param[graph] - the cfg to traverse
 * @param[lattice] - the lattice defining join and equiv of results.
 * @param[initial] - the initial lattice
 * @param[direction] - the direction of the cfg traversal
 */
abstract class BlockDataflowAnalysis<Graph, Block, @Treapable BlockLabel, T : Any>(
    val graph: Graph,
    val lattice: JoinLattice<T>,
    val initial: T,
    val direction: Direction,
    private val blockView: GraphBlockView<Graph, Block, BlockLabel>,
) {
    fun T.join(other: T): T = lattice.join(this, other)
    fun T.equiv(other: T): Boolean = lattice.equiv(this, other)

    val blockIn = mutableMapOf<BlockLabel, T>()
    val blockOut = mutableMapOf<BlockLabel, T>()

    /**
        Optional "finalizer" to allow state to be cleaned up after it will no longer be used for analysis.  Use this
        to reduce memory usage by discarding temporary data that is used in the dataflow analysis, but doesn't need
        to be present in the final result.
     */
    protected open val finalizer: Finalizer? = null

    protected abstract inner class Finalizer {
        open fun finalizeBlock(block: Block) {}
        abstract fun finalizeState(state: T): T
    }

    private fun next(b: Block): Collection<Block> =
        when (direction) {
            Direction.FORWARD -> blockView.succ(graph, b)
            Direction.BACKWARD -> blockView.pred(graph, b)
        }

    /**
     * Processing of the current block
     */
    abstract fun transform(inState: T, block: Block): T

    /**
     * Running the analysis in (forward/backward according to direction) BFS until fixed point
     */
    protected open fun runAnalysis() {
        val sccGraph = SCCGraph(blockView.blockGraph(graph))
        val order = topologicalOrder(sccGraph.sccGraph).let {
            when (direction) {
                Direction.FORWARD -> it.reversed()
                Direction.BACKWARD -> it
            }
        }
        val initialBlocks =
            when (direction) {
                Direction.FORWARD -> sccGraph.roots
                Direction.BACKWARD -> sccGraph.leaves
            }
        for (block in initialBlocks) {
            blockIn[block] = initial
        }
        for (sccIndex in order) {
            runOnSCC(sccGraph.sccs[sccIndex]!!)
        }
    }

    open protected fun filterNext(succ: Collection<BlockLabel>,
        currBlock: BlockLabel, postState: T): Collection<BlockLabel> = succ

    /**
     * In each SCC we run until a fixed point.
     *
     * We run in reversed post order on the nodes of the SCC. This is a good heuristic for having most of a node's
     * predecessor already processed.
     */
    private fun runOnSCC(sccBlocks: Set<BlockLabel>) {
        val inputBlocks = sccBlocks.filter { it in blockIn }
        val order = postOrder(
            // taking the first is enough, because this is an SCC.
            start = listOf(inputBlocks.firstOrNull() ?: return) as Collection<BlockLabel>,
            nexts = { bid ->
                next(blockView.elab(graph, bid))
                    .map { blockView.blockId(it) }
                    .filter { it in sccBlocks }
            }
        ).reversed()

        val changed = inputBlocks.toMutableSet()

        fun addToChanged(id: BlockLabel) {
            if (id in sccBlocks) {
                changed += id
            }
        }
        while (changed.isNotEmpty()) {
            for (blockId in order) {
                if (blockId in changed) {
                    changed -= blockId
                    val start = blockIn[blockId]!!
                    val block = blockView.elab(graph, blockId)
                    val result = transform(start, block)
                    val prevResult = blockOut[blockId]
                    // update and queue
                    if (prevResult?.equiv(result) != true) {
                        blockOut[blockId] = result
                        val nextIds = next(block).map { blockView.blockId(it) }
                        filterNext(nextIds, blockId, result).forEach { nxtId ->
                            if (nxtId in blockIn) {
                                val currStart = blockIn[nxtId]!!
                                val joinIn = currStart.join(result)
                                // maybe the result changed but it doesn't really have an effect
                                if (!joinIn.equiv(currStart)) {
                                    blockIn[nxtId] = joinIn
                                    addToChanged(nxtId)
                                }
                            } else {
                                blockIn[nxtId] = result
                                addToChanged(nxtId)
                            }
                        }
                    }
                }
            }
        }

        finalizer?.apply {
            inputBlocks.forEach {
                blockIn[it] = finalizeState(blockIn[it]!!)
                blockOut[it] = finalizeState(blockOut[it]!!)
                finalizeBlock(blockView.elab(graph, it))
            }
        }
    }
}
