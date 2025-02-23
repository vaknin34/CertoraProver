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

package analysis.opt.intervals

import analysis.*
import analysis.dataflow.groupToArrays
import com.certora.collect.*
import datastructures.add
import datastructures.buildMultiMap
import datastructures.stdcollections.*
import tac.NBId
import utils.*
import vc.data.TACSymbol
import vc.data.freeVars
import vc.data.isNonTrivialAssert

/**
 * This is a special use/def site analyser used in [IntervalsCalculator].
 *
 * The general idea is the querying a variable at point:
 *   1. Traversing backward in the graph, we wish to get the first use/def sites we encounter.
 *      * if we "fell off" the graph in this traversal, we return null.
 *   2. Traversing forward, we return the first use site we encounter
 *      * again, falling off the graph, the returned value is null.
 *      * An assert is seen as falling of the graph, because for our purposes it is a conditional jump, where one branch
 *        is an invisible leaf.
 *      * A def site for the variable is also seen as falling off the graph, because the original incarnation of the
 *        variable essentially disappears at this point.
 */
class SiteAnalysis(private val g: TACCommandGraph) {

    private val dom = g.cache.domination

    private fun TACSymbol.Var.takeIfGoodTag() =
        takeIf { tag.isPrimitive() }

    private fun Iterable<TACSymbol.Var>.filterGoodVars() =
        mapNotNull { it.takeIfGoodTag() }

    /** (block, v) -> pos */
    private val defSites: Map<Pair<NBId, TACSymbol.Var>, IntArray> =
        groupToArrays(
            g.commands.mapNotNull { (ptr, cmd) ->
                cmd.getLhs()?.takeIfGoodTag()?.let {
                    (ptr.block to it) to ptr.pos
                }
            }
        )

    /** (block, v) -> pos */
    val useSites: Map<Pair<NBId, TACSymbol.Var>, IntArray> =
        groupToArrays(
            g.commands.flatMap { (ptr, cmd) ->
                cmd.getFreeVarsOfRhs().filterGoodVars().map {
                    (ptr.block to it) to ptr.pos
                }
            }
        )


    /** This is a function so that the result can be discarded. */
    fun varUsageBlocks() = buildMultiMap {
        useSites.keys.forEach { (b, v) -> add(v, b) }
    }

    private inline fun lastPtrOrNull(b: NBId, v: TACSymbol.Var, predicate: (Int) -> Boolean = { true }): CmdPointer? {
        val lastUse = useSites[b to v]?.lastOrNull(predicate)
        val lastDef = defSites[b to v]?.lastOrNull(predicate)
        return when {
            lastUse == null -> lastDef
            lastDef == null -> lastUse
            else -> maxOf(lastDef, lastUse)
        }?.let {
            CmdPointer(b, it)
        }
    }

    /** block -> positions */
    private val asserts = groupToArrays(
        g.commands
            .filter { (_, cmd) -> isNonTrivialAssert(cmd) }
            .map { (ptr, _) -> ptr.block to ptr.pos }
    )


    /**
     * Variables that have all their def and use in one block. Normally, around 80% of the variables are "easy".
     * These get special treatment in the backwards analysis case for efficiency's sake.
     *
     * Note that such variables disappear as soon as they appear in the data-flow calculation of the forward use
     * analysis case, and so this map is not used there.
     */
    private val easyBackwardsQueryVars = buildUnorderedMap<TACSymbol.Var, NBId> {
        val badVars = mutableSetOf<TACSymbol.Var>()
        fun process(blockAndVar: Pair<NBId, TACSymbol.Var>) {
            val (b, v) = blockAndVar
            if (v !in badVars) {
                this[v]?.let {
                    if (it != b) {
                        badVars += v
                    }
                } ?: this.put(v, b)
            }
        }
        defSites.keys.forEach(::process)
        useSites.keys.forEach(::process)
        badVars.forEach { this -= it }
    }


    private data class SitesState(
        val sites: TreapMap<TACSymbol.Var, TreapSet<CmdPointer>>,
    )

    /**
     * if a variable is undefined, then it's also considered undefined in the join.
     * This is consistent with our null-on-null behavior
     */
    private fun join(a: SitesState, b: SitesState) = SitesState(
        sites = a.sites.parallelIntersect(b.sites) { _, aa, bb -> aa + bb }
    )

    /**
     * For each block, holds for each variable the set of cmdPointers that are the first use or def sites for this
     * variable, that we would encounter if we traversed backward from right before this block. If we can "fall off"
     * the graph in this traversal, i.e., the variable at the beginning of the block may be uninitialized, then the
     * variable is dropped from the map.
     *
     * Easy variables are not considered here, as they can be handled in a simpler manner.
     */
    private val backwardEntryStates: Map<NBId, SitesState> by lazy {
        object : TACBlockDataflowAnalysis<SitesState>(
            g,
            JoinLattice.ofJoin(::join),
            SitesState(treapMapOf()),
            Direction.FORWARD
        ) {
            override fun transform(inState: SitesState, block: TACBlock): SitesState {
                val sites = inState.sites.builder()
                block.commands.forEach { (ptr, cmd) ->
                    cmd.freeVars()
                        .filterGoodVars()
                        .filter { it !in easyBackwardsQueryVars }
                        .forEach { v -> sites[v] = treapSetOf(ptr) }
                }
                return SitesState(sites.build())
            }

            init {
                runAnalysis()
            }
        }.blockIn
    }


    /**
     * returns the backwards sites of [v] at the rhs of [queryPtr]
     */
    fun backwardsSitesOf(queryPtr: CmdPointer, v: TACSymbol.Var): TreapSet<CmdPointer>? {
        require(v.tag.isPrimitive()) { "Variable $v's Tag ${v.tag} not supported" }
        val (queryBlock, queryPos) = queryPtr

        // check if there is a use/def site in the same block, before the query point.
        lastPtrOrNull(queryBlock, v, predicate = { it < queryPos })
            ?.let { return treapSetOf(it) }

        // v is easy, all use/def sites are in the same block.
        easyBackwardsQueryVars[v]?.let { sitesBlock ->
            // the special case where the query is before all the sites.
            if (sitesBlock == queryBlock) {
                return null
            }
            // otherwise, the sites block must dominate the query block for a non null answer.
            return runIf(dom.dominates(sitesBlock, queryBlock)) {
                treapSetOf(lastPtrOrNull(sitesBlock, v)!!)
            }
        }
        return backwardEntryStates[queryPtr.block]!!.sites[v]
    }


    /**
     * For each block, holds for each variable the set of cmdPointers that are the first use sites for this variable,
     * that we would encounter if we traversed forward from right after this block. If we can "fall off"
     * the graph in this traversal, i.e., we hit a def site, we hit an assert, or a block has no successor, then the
     * variable is dropped from the map.
     *
     * Easy variables are not considered here, as they can be handled in a simpler manner.
     */
    private val usageExitStates: Map<NBId, SitesState> =
        object : TACBlockDataflowAnalysis<SitesState>(
            g,
            JoinLattice.ofJoin(::join),
            SitesState(treapMapOf()),
            Direction.BACKWARD
        ) {
            override fun transform(inState: SitesState, block: TACBlock): SitesState {
                var newState = inState.sites.builder()
                block.commands.asReversed().forEach { (ptr, cmd) ->
                    if (isNonTrivialAssert(cmd)) {
                        newState = treapMapBuilderOf()
                    } else {
                        cmd.getLhs()
                            ?.takeIfGoodTag()
                            ?.let { newState -= it }
                    }
                    cmd.getFreeVarsOfRhs()
                        .filterGoodVars()
                        .forEach { newState[it] = treapSetOf(ptr) }
                }
                return SitesState(newState.build())
            }

            init {
                runAnalysis()
            }
        }.blockIn


    /**
     * Gets the first forward use sites of [v] ignoring the cmd at [queryPtr] itself.
     * The only case
     */
    fun forwardUseSitesOf(queryPtr: CmdPointer, v: TACSymbol.Var): Set<CmdPointer>? {
        require(v.tag.isPrimitive()) { "Variable $v's Tag ${v.tag} not supported" }
        val (queryBlock, queryPos) = queryPtr

        // check if there is a use site in the same block, after the query point.
        useSites[queryBlock to v]
            ?.firstOrNull { it > queryPos }
            ?.let { usePos ->
                return when {
                    // there is a non-trivial assert between the query site and the use site
                    asserts[queryBlock]?.any { it in queryPos..<usePos } == true -> null
                    // there is a def-site after the query site and before the use site
                    defSites[queryBlock to v]?.any { it in queryPos + 1..<usePos } == true -> null
                    else -> setOf(CmdPointer(queryBlock, usePos))
                }
            }

        // there's an assert right after the query point, blocking our search forward.
        asserts[queryBlock]?.lastOrNull()?.let {
            if (it >= queryPos) {
                return null
            }
        }

        // same but with a def site.
        defSites[queryBlock to v]?.lastOrNull()?.let {
            if (it > queryPos) {
                return null
            }
        }

        return usageExitStates[queryBlock]!!.sites[v]
    }

}



