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

package analysis.split

import algorithms.*
import analysis.*
import annotations.PerformanceCriticalUsesOnly
import datastructures.ArrayHashSet
import datastructures.get
import datastructures.mutableNestedMapOf
import datastructures.set
import datastructures.stdcollections.*
import tac.NBId
import utils.*
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACSymbol

/**
 * Analyzes the domination graph so as to be able to answer efficiently [getDefinitiveDef], which returns the
 * definition that is guaranteed to be the one defining this variable at this point.
 *
 * The preprocessing is more demanding than our standard def analysis as it needs the transitive closure of the block
 * graph. Therefore, it's probably wise to use this only when we know it's going to be used a lot.
 */
class DefiniteDefSites(val code: CoreTACProgram) {
    private val graph = code.analysisCache.graph
    private val dom = code.analysisCache.domination
    private val scc = SCCGraphInfo(graph.blockSucc)
    private val graphReachability by lazy { transitiveClosure(graph.blockSucc, reflexive = true) }

    private fun canReach(from: NBId, to: NBId) =
        graphReachability[from]?.contains(to) == true

    private infix fun NBId.dominates(o: NBId) =
        dom.dominates(this, o)

    /** Keeps for each var, for each block, the indices where it is defined (sorted) */
    private val defSites = mutableNestedMapOf<TACSymbol.Var, NBId, List<Int>>().also { nestedMap ->
        for ((block, cmds) in graph.blocks) {
            cmds.mapNotNull { it.maybeNarrow<TACCmd.Simple.AssigningCmd>() }
                .groupBy { it.cmd.lhs }
                .forEachEntry { (lhs, cmds) ->
                    nestedMap[lhs, block] = cmds.map { it.ptr.pos }.sorted()
                }
        }
    }

    /**
     * if there is a site that surely defines [v] at [ptr] then return it, and otherwise null.
     */
    fun getDefinitiveDef(ptr: CmdPointer, v: TACSymbol.Var): CmdPointer? {
        val defSitesV = defSites[v] ?: return null

        val defSitesInBlock = defSitesV[ptr.block]

        val blocks = if (defSitesInBlock != null) {
            // If there is one in its own block then it is the last one before `ptr` (if they are after, we keep looking).
            defSitesInBlock.findLast { it < ptr.pos }?.let { pos ->
                return CmdPointer(ptr.block, pos)
            }
            if (scc.isInLoop(ptr.block)) {
                // there is a def site after this point in the same block, and the block participates in a loop.
                // as we must enter the loop from somewhere, we get that there are at least two def sites (one may be
                // just uninitialized).
                return null
            }
            if (defSitesV.size == 1) {
                // the only def sites are in this block after this point, and so the var is uninitialized.
                return null
            } else {
                // def sites in this block are not interesting.
                defSitesV.keys - ptr.block
            }
        } else {
            defSitesV.keys
        }

        // Since domination is a tree, then of all the dominating sites for our query point, we care only for the last
        // one, the others are overwritten by it, and so are irrelevant.
        val dominatingBlocks = blocks.filter { it dominates ptr.block }
        if (dominatingBlocks.isEmpty()) {
            return null
        }
        val candidate =
            dominatingBlocks.maxOfWith({ a: NBId, b: NBId ->
                when {
                    a == b -> 0
                    a dominates b -> -1   // meaning a<=b, so higher up in the tree.
                    b dominates a -> 1
                    else -> error("Domination is not a tree??")
                }
            }) { it }

        // This is the only ptr that may qualify as a definite def site of `ptr`
        fun candidatePtr() =
            CmdPointer(candidate, defSites[v, candidate]!!.last())

        if (blocks.size == dominatingBlocks.size) {
            return candidatePtr()
        }

        // These are the def sites that may interfere with the dominance of `candidate`.
        val toCheck = blocks - dominatingBlocks

        if (scc.isDag) {
            // Check that no other def site interferes with the assignment at candidate
            if (toCheck.any { site ->
                    canReach(site, ptr.block) && canReach(candidate, site)
                }) {
                return null
            }
            return candidatePtr()
        }

        // It's not a DAG so the above trick doesn't apply.
        // We traverse backwards in the graph and if we find any of `toCheck` before finding `candidate` it's game over.
        val visited = ArrayHashSet<Any?>(127)
        val workList = ArrayDeque<Any?>(100)
        val toCheckUnytyped = toCheck as Set<Any?>
        @OptIn(PerformanceCriticalUsesOnly::class)
        workList += graph.predUntyped(ptr.block)

        workList.consume {
            it.uncheckedAs<Set<Any>>().forEach { block ->
                if (block in toCheckUnytyped) {
                    return null
                }
                // if we reached our candidate, no need to keep going.
                if (block != candidate && visited.add(block)) {
                    @OptIn(PerformanceCriticalUsesOnly::class)
                    workList += graph.predUntyped(block)
                }
            }
        }
        return candidatePtr()
    }

}
