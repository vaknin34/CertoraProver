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

package instrumentation.transformers

import algorithms.SimpleDominanceAnalysis
import allocator.Allocator
import analysis.TACCommandGraph
import analysis.maybeAnnotation
import analysis.maybeNarrow
import analysis.worklist.StepResult
import analysis.worklist.VisitingWorklistIteration
import com.certora.collect.*
import config.Config
import datastructures.MutableReversibleDigraph
import datastructures.ReversibleDigraph
import datastructures.stdcollections.*
import tac.NBId
import utils.*
import vc.data.*

/**
 * Instruments branch start and end snippets in cases where these can be definitely detected and have source maps,
 * and skipping loop iterations.
 */
object BranchSnippetInstrumenter {
    fun instrumentBranchSnippets(p: CoreTACProgram): CoreTACProgram {
        if (p.destructiveOptimizations) {
            // save the work if we ignore calltrace
            return p
        }

        if (!Config.EnableConditionalSnippets.get()) {
            // feature-flag turned off
            return p
        }

        val g = p.analysisCache.graph
        val reverseToposort = p.topoSortFw.reversed() // program should have no loops by this point

        /* Initially this analysis ran on rules, and we know that in rules,
         reverting paths which are _usually_ pruned, meaning that all branches with reverting paths
         will only end (by postdomination) at the end of the function call.
         This is not very interesting because the function's execution end will close the scope anyway.
         The same logic applies for 'returns' in the middle of the function.
         (so when we ran this analysis on rules we got 'lucky' that many of the reverting paths were pruned via `getSafeBranches`.)
         To generalize, therefore, if there's a branch leading to a halting command,
         we can 'imagine' it does not reach the halting command,
         just for the sake of immediate postdominators computation.
         Is this precise? of course not! We could have branches inside definitely-reverting code blocks
         that are not at the end of the function, e.g.:
         ```
         if (revertCond1 || revertCond2) {
            string msg;
            if (revertCond1) { msg = "msgFor1"; } else { msg = "msgFor2"; }
            revert(msg);
         }
         ```
         Snippets for `if (revertCond1)` may end opening a scope that ends in a non-matching sink (due to our modification of the graph).

         Other heuristics, such as assuming we always finish with `return`,
         are also wrong for a code such as `while(cond) { ... if (..) { return; } }; revert();`
         As a compromise, we will assume for the most boring case:
         the function ends with a return, reverts are ignored, return immediately inside branches are also ignored. */
        val ipostdomRel = SimpleDominanceAnalysis(noMiddleHalt(g).asReversed()).immediatelyDominatedBy
        val branchPtrsWithSrcMap = g.commands.mapNotNull { lcmd ->
            lcmd.maybeNarrow<TACCmd.Simple.JumpiCmd>()
                ?.let { jumpi ->
                    // condense the content in case it's the full contract. We do want to have 2 lines at least... unless it's full contract
                    jumpi `to?` jumpi.cmd.metaSrcInfo?.getSourceDetails()?.let { src ->
                        when {
                            src.content.isFullContractSrcMap() -> src.copy(content = src.content.condense(1))
                            src.content.isFullFunctionSrcMap() -> src.copy(content = "compiler-generate condition${
                                src.content.condenseBlock()?.let { " in $it" }.orEmpty()}"
                            )
                            src.content.isIfConditionSrcMap() -> src.copy(
                                content = src.content.condenseBlock() ?: src.content
                            )
                            else -> src.copy(content = src.content.condense(2))
                        }
                    }
                }
        }
            .filter { (ptr, _) ->
                // filter out if cannot find immediate postdominator `ip`, or `ip` is starting with a loop.end snippet
                val ip = ipostdomRel[ptr.ptr.block] ?: return@filter false
                val block = g.elab(ip)
                // if first command is EndLoopSnippet we filter out, if it's not we keep
                // note that in case of conditional breaks/returns inside loops, the nice structuring of snippets won't be kept anyway,
                // so branch snippet balancing should be handled gracefully and not necessarily hierarchically.
                // specifically: seeing a loop.end snippet should automatically close all open branches,
                // and branch.end snippets will skip if the current stack top is not branch.start
                block.commands.isNotEmpty() && block.commands.first()
                    .maybeAnnotation(TACMeta.SNIPPET)?.takeIf { it is SnippetCmd.EVMSnippetCmd.LoopSnippet.EndLoopSnippet } == null
                    // to consider: check also EndIterSnippet?
            }.sortedBy { (ptr, _) ->
                // sort by reverse topological order, as we wish to add the end snippet of the first-appearing start snippet _last_.
                reverseToposort.indexOf(ptr.ptr.block)
            }

        val patched = p.patching {
            val branchEndToSnippets = mutableMapOf<NBId, MutableList<TACCmd.Simple.AnnotationCmd>>() // there could be multiple end snippets per branch end
            branchPtrsWithSrcMap.forEach { (branchStart, srcmap) ->
                val ip = ipostdomRel[branchStart.ptr.block]!! // guaranteed from filter above
                val branchId = Allocator.getFreshId(Allocator.Id.BRANCH)
                it.addBefore(branchStart.ptr,
                    listOf(SnippetCmd.EVMSnippetCmd.BranchSnippet.StartBranchSnippet(branchId, srcmap).toAnnotation(p.destructiveOptimizations))
                )
                // adds end snippet to the end of the list, so the last added should be the first in topological order
                // in order to keep the 'trace' structure correctly balanced
                branchEndToSnippets.computeIfAbsent(ip) { mutableListOf() }
                    .add(SnippetCmd.EVMSnippetCmd.BranchSnippet.EndBranchSnippet(branchId).toAnnotation(p.destructiveOptimizations))
            }

            branchEndToSnippets.forEachEntry { (branchEnd, snippets) ->
                it.addBefore(g.elab(branchEnd).commands.first() /* safe from filter above */ .ptr ,
                    snippets
                )
            }

            // we also want to add snippets for return/revert
            g.commands.filter { it.cmd.isHalting()  }.forEach { haltingLCmd ->
                val range = haltingLCmd.cmd.sourceRange()
                val haltSnippet = when(haltingLCmd.cmd) {
                    is TACCmd.Simple.ReturnCmd, is TACCmd.Simple.ReturnSymCmd -> SnippetCmd.EVMSnippetCmd.HaltSnippet.Return(range)
                    is TACCmd.Simple.RevertCmd -> SnippetCmd.EVMSnippetCmd.HaltSnippet.Revert(range)
                    else -> throw IllegalStateException("Unknown halting command $haltingLCmd")
                }
                it.addBefore(haltingLCmd.ptr, listOf(haltSnippet.toAnnotation(p.destructiveOptimizations)))
            }

        }

        return patched
    }

    /**
     * get rid of reverting paths, assumes, and returns under branches.
     * see caller for explanation of why this functions is implemented in this seemingly arbitrary fashion
     */
    private fun noMiddleHalt(g: TACCommandGraph): ReversibleDigraph<NBId> {
        val sinks = g.sinks
        if (sinks.size == 1) {
            // very boring graph
            return MutableReversibleDigraph(g.blockGraph)
        }

        // ideally just one 'ultimate' sink, but as explained, not really doable. could also be empty! i.e. all-reverting function
        val ultimateSinks = sinks.filter { sinkLCmd ->
            sinkLCmd.cmd !is TACCmd.Simple.RevertCmd // not a revert
                && sinkLCmd.cmd !is TACCmd.Simple.AssumeCmd // not an assume (probably assume false, but doesn't matter)
                && (g.pred(sinkLCmd.ptr).size > 1  // has multiple predecessors
                || g.pred(sinkLCmd.ptr).single()/* must succeed or, if our sink has no predecessor, it means we would definitely have a single sink and return before */
                    .let { pred -> g.succ(pred).size == 1 }) // single predecessor, not under a branch
        }.let { ultimateSinksFirstRound ->
            ultimateSinksFirstRound.ifEmpty {
                // this is not so fun, so let's try to keep the return nodes and if the branch snippets are confusing, so be it
                sinks.filter { sinkLCmd -> sinkLCmd.cmd is TACCmd.Simple.ReturnCmd }
            }
        }

        // this code is very similar to getSafeBranches, but uses a proper worklist
        val nodesToRemove = mutableSetOf<NBId>()
        sinks.mapNotNullTo(nodesToRemove) { it.takeIf { it !in ultimateSinks }?.ptr?.block }

        val toRemoveCompute = object : VisitingWorklistIteration<NBId, Unit, Unit>() {
            override fun process(it: NBId): StepResult<NBId, Unit, Unit> {
                val pred = g.pred(it)
                    .filter { parent -> g.succ(parent).all { it in nodesToRemove } }
                        .also { nodesToRemove.addAll(it) }

                return StepResult.Ok(pred, emptyList())
            }

            override fun reduce(results: List<Unit>) {}
        }

        toRemoveCompute.submit(nodesToRemove.toList())

        val nodesToFix =
            g.blockGraph.filter { it.key !in nodesToRemove && it.value.containsAny(nodesToRemove) }
                .keys

        val newGraph = g.blockGraph
            .filterNot { it.key in nodesToRemove }
            .mapValues { entry ->
                if (entry.key in nodesToFix) {
                    entry.value.minus(nodesToRemove)
                } else {
                    entry.value
                }
            }

        return MutableReversibleDigraph(newGraph)
    }
}
