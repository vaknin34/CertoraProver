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

import analysis.TACCommandGraph
import analysis.getNaturalLoops
import analysis.ip.INTERNAL_FUNC_EXIT
import analysis.ip.INTERNAL_FUNC_START
import analysis.maybeAnnotation
import analysis.worklist.IWorklistScheduler
import analysis.worklist.StepResult
import analysis.worklist.WorklistIteration
import com.certora.collect.*
import datastructures.PersistentStack
import datastructures.persistentStackOf
import datastructures.stdcollections.*
import datastructures.topOrNull
import log.*
import tac.NBId
import utils.*
import vc.data.CoreTACProgram
import vc.data.PatchingTACProgram
import vc.data.SimplePatchingProgram
import vc.data.TACCmd

private data class EdgeTuple(val src: NBId, val dst: NBId)

private typealias StackTrace = TreapMap<TreapList<EdgeTuple>, PersistentStack<Int>>

private val logger = Logger(LoggerTypes.SUMMARIZATION)

/**
 * An analysis that handles mismatched stacks that can be generated by the solidity compiler. This can
 * occur due to solidity sharing exit blocks between two internal function invocations, like so:
 * ```
 * if(*) {
 *    enter f()
 *    ...
 *    goto l;
 * } else {
 *   enter g()
 *   ...
 *   goto l;
 * }
 * l:
 * exit g()
 * exit f()
 * ```
 *
 * Of course, depending on which path you take through the program, the internal call stack will be incoherent:
 * we'Ll be tasked with popping a frame that isn't on the stack.
 *
 * This Fixup solves the issue by simulating the internal call stack throughout execution of the program (this is the [StackTrace]).
 * When it detects an error (i.e., exeuction can reach the same point with two different call stacks) it records
 * the *set* of potential call stacks (this is why [StackTrace] is a map), and the paths along which the mismatch happened (this
 * is the [TreapList] of [EdgeTuple] in the domain of the map). The analysis then
 * continues optimistically executing, hoping to find a point in the program where the mismatch is resolved.
 *
 * Mismatch resolution is defined as a point in the program where all mismatched stacks end up being the same. We find this
 * point by interpreting pop `f` commands on the stacks in the trace which have `f` as the top activation record, and ignoring
 * it for the other members of the trace. Let us return to the set of stacks in our example above. We reach the join point
 * `l` with two stacks `{f}` and `{g}`. The first command pops `g`, so we apply this to the relevant stack, yielding `{f}` and `{}`.
 * Next, we pop `f`, which we apply to the other stack giving us `{}` and `{}`, i.e., two equal stacks.
 *
 * Why is this property what we want? Well, it suggests that by starting from the point of mismatch (in this case `l`) and
 * creating a duplicate path of execution through the program for each initial stack, we can create an equivalent program
 * without "too much" disruption. To give an idea about what this duplication looks like, consider the following equivalent program to the above:
 * ```
 * // as above
 * if(*) {
 *    enter f();
 *    ...
 *    goto l';
 * } else {
 *    enter g();
 *    ...
 *    goto l'';
 * }
 * l':
 *   nop;
 *   exit f();
 *   goto j;
 * l'':
 *   exit g();
 *   nop;
 *   goto j;
 * j: ...
 *
 * ```
 * Here we have duplicated the path starting at `l`, but erased the `exit g()` if we are coming from the true branch of the conditional,
 * and vice versa if we're coming from the else branch. Note that the duplication is "limited": after the stacks are once again
 * in agreement, execution rejoins a common path at `j`.
 *
 * NB that it would always be "safe" to just duplicate blocks infinitely to resolve stack
 * mismatches, but this can cause an exponential blow up in the program. By focusing on the areas delimited by this analysis, we
 * can ensure much smaller rewrites.
 *
 * To sum up: this analysis finds points in the program at which there is disagreement about the internal call stack.
 * It traces a path of execution P forward until it sees enough `pop` commands to rectify this disagreement. Then
 * it duplicates the discovered path `P`, once for each mismatched stack. For each such (duplicated path, mismatched stack),
 * we keep only the `pop` commands along that path match the records on the mismatched stack.
 */
object InternalReturnFixup {
    /**
     * A [StackTrace] is the datastructure that collects the set of potential stacks at a program point.
     * It is actually a map from a list of edges to a stack of activation records. The edges
     * in the key *disambiguate* which path was taken to yield the path in the key. If the key is
     * the empty list, then there is no disambiguation required: there is a single known stack that
     * holds at some point. However, if we have:
     * ```
     * A -> B = {l}
     * C -> B = {k}
     * ```
     * This means that we have a stack `{l}` which reached this point in the program by traversing the edge from block A -> B.
     * We also have a stack `{k}` which reached this point by traversing the edge C -> B. The reader will note that
     * the two keys share a destination block: this is because mismatches will always happen at a join point.
     *
     * Note that we only extend these lists edges when needed to disambiguate. For example, if the above state
     * were to move from B to D, we do NOT automatically add `B -> D` to the list in the keys, as it does nothing to
     * disambiguate paths.
     *
     * However, we can see these keys grow to cardinality > 1. Let us take the previous state, which was deduced to hold
     * at block B, that is: block B is reachable from block A and block C, and the stack is `{l} in the former case
     * and {k} in the latter. Suppose then we follow an edge from B to E. E also has a predecessor F, where we had
     * stack `{m}`. Then we *would* extend the error traces to disambiguate how we got the
     * different stack at block E, yielding the following:
     *
     * ```
     * A -> B, B -> E = {l}
     * C -> B, B -> E = {k}
     * F -> E = {m}
     * ```
     * In other words, we can reach `E` with stack `{l} by first following A to B, then following B to E. OR, we can
     * reach `E` in stack {k}, by first following C to B, then following B to E. Or, finally, we can reach `E` in stack {m},
     * by following F to E.
     *
     * To reiterate, the above discussion is only relevant if there is a mismatch. In the (common) case that there is singular
     * stack at a program point, the [StackTrace] is a singleton map with the empty list as the key. The list of edges is not
     * used as a general trace of execution (our analysis wouldn't terminate if so!) but only for limited disambiguation.
     */


    /**
     * This function is used in the error extension case when we detect that new stacks are being merged together.
     * It corresponds to added `B -> E` onto `A -> B` and C -> B` in the above examples.
     */
    private fun StackTrace.extendError(from: NBId, to: NBId) = this.mapKeys { (k, _) ->
        k + EdgeTuple(from, to)
    }

    /**
     * Does this state represent a mismatch stack? That is, do we have multiple mappings, or
     * do we not have the empty list as a key in the map. NB looking at the implementations of our state management,
     * *either* of these conditions are sufficient, but we check both just to be certain.
     */
    private fun StackTrace.isErrorTrace() = this.size != 1 || treapListOf() !in this

    /**
     * Called to simulate entering a new function. Note that we do not allow this
     * if we have a mismatched stack, in other words we expect this mismatch to appear
     * in the limited "suffix" of some handful of function returns before "real" execution starts.
     */
    private fun StackTrace.tryPush(i: Int) : Either<StackTrace, String> {
        return if(isErrorTrace()) {
            this.mapValues { (_, v) ->
                v.push(i)
            }.toLeft()
        } else {
            treapMapOf(
                treapListOf<EdgeTuple>() to this[treapListOf()]!!.push(i)
            ).toLeft()
        }
    }

    /**
     * If all stacks are in agreement, drop all of our disambiguating context, we don't need it anymore.
     */
    private fun StackTrace.normalize() : StackTrace {
        val norm = this.values.uniqueOrNull()
        if(norm != null) {
            return treapMapOf(treapListOf<EdgeTuple>() to norm)
        }
        return this
    }

    /**
     * Pop the activation record with [i] from the relevant stacks. If no stacks in the collection
     * match [i], abort with an error: something very suspicious is happening.
     *
     * Otherwise, update those stacks for which [i] is on the top, leaving the others unchanged.
     */
    private fun StackTrace.pop(i: Int) : Either<StackTrace, String> {
        if(this.none { (_, d) ->
                d.topOrNull() == i
            }) {
            return "$i is not on the stack".toRight()
        }
        return this.mapValues { (_, stk) ->
            if(stk.topOrNull() == i) {
                stk.pop()
            } else {
                stk
            }
        }.toLeft()
    }

    /**
     * Runs the analysis above on [c], finding places where stack mismatches can be resolved by limited
     * duplication of code paths.
     */
    fun transform(c: CoreTACProgram): CoreTACProgram {
        val g = c.analysisCache.graph
        /**
         * Records the out state of every block
         */
        val blockOut = treapMapBuilderOf<NBId, StackTrace>()
        val loops = getNaturalLoops(g)
        val loopHeads = loops.mapToSet { it.head }

        /**
         * Records the in state of every block, the join over all of its predecessors.
         * Blocks for which the stack trace is not an error trace indicate where we can stop duplication
         * later.
         */
        val blockIn = treapMapBuilderOf<NBId, StackTrace>()
        val worker = object : WorklistIteration<NBId, Unit, String?>() {
            /**
             * A note on iteration order: we do not allow mismatched stacks to traverse backjumps, this scenario
             * is both deeply unlikely (fingers crossed) and pretty hard to reason about. Thus, we can basically
             * make a single breadth first traversal through the program, as we can "skip" any backjumps, assuming
             * the stack propagated back to the head of the loop is the same as the stack entering the loop
             * (if this assumption does not hold, this analysis aborts with an error).
             */
            override val scheduler: IWorklistScheduler<NBId> = c.analysisCache.naturalBlockScheduler

            private fun getBlockStartState(it: NBId) : Either<StackTrace, String> {
                val pred = g.pred(it)
                if (pred.size == 0) {
                    return treapMapOf(treapListOf<EdgeTuple>() to persistentStackOf<Int>()).toLeft()
                }
                val validPreds = mutableListOf<Pair<NBId, StackTrace>>()
                for (p in pred) {
                    /**
                     * A predecessor which we dominate is the tail of a loop, so we skip this predecessor
                     * (but verify below that when propagating state back we aren't introducing a mismatch)
                     */
                    if (g.cache.domination.dominates(it, p)) {
                        continue
                    }
                    /**
                     * Then something has gone wrong, we were scheduled before a block that could reach us
                     * should have finished. The [analysis.worklist.NaturalBlockScheduler] broke!
                     */
                    if (p !in blockOut) {
                        return "No recorded out state for predecessor $p of block $it".toRight()
                    }
                    validPreds.add(p to blockOut[p]!!)
                }
                if (validPreds.isEmpty()) {
                    return "No predecessors found for $it".toRight()
                }
                /**
                 * If all of the predecessor states are the same, there is no need for disambiguation
                 * (that's what uniqueOrNull does).
                 *
                 * Otherwise introduce a disambiguation edge into each record in each map in our predecessors.
                 */
                val st = validPreds.map { it.second }.uniqueOrNull() ?: validPreds.map { (pred, m) ->
                    m.extendError(from = pred, to = it)
                }.reduce { a, b ->
                    a + b
                }.also { m ->
                    logger.info {
                        "Entering $it, have error trace $m"
                    }
                }
                return st.toLeft()
            }

            /**
             * Used for sanity, to make sure we don't loop our analysis
             */
            private val visited = mutableSetOf<NBId>()

            override fun process(it: NBId): StepResult<NBId, Unit, String?> {
                /**
                 * As always, let's pretend revert blocks don't exist
                 */
                if(it in g.cache.revertBlocks) {
                    return this.cont(listOf())
                }
                if(!visited.add(it)) {
                    return this.halt("We somehow have reached $it again, despite not following loop backjumps")
                }
                var st = when(val r = getBlockStartState(it)) {
                    is Either.Left -> r.d
                    is Either.Right -> return this.halt(r.d)
                }
                /**
                 * Don't allow error states within a loop, that duplication might spin out? The rewrite would
                 * also just be annoying.
                 */
                if(it in loopHeads && st.isErrorTrace()) {
                    return this.halt("About to enter a loop with an error stack, this is very bad")
                }
                blockIn[it] = st
                if(st.values.map { it.size }.uniqueOrNull() == null) {
                    return this.halt("At $it, have mismatch stack heights")
                }
                /**
                 * The actual abstract interpretation is pretty simple, we only interpret push and pop for
                 * for the internal call stack operations and ignore everything else.
                 */
                for(l in g.elab(it).commands) {
                    val enter = l.maybeAnnotation(INTERNAL_FUNC_START)
                    val exit = l.maybeAnnotation(INTERNAL_FUNC_EXIT)
                    if(enter != null) {
                        st = when(val r = st.tryPush(enter.id)) {
                            is Either.Left -> r.d
                            is Either.Right -> return this.halt("At push $l: ${r.d}")
                        }
                    } else if(exit != null) {
                        st = when(val r = st.pop(exit.id)) {
                            is Either.Left -> r.d
                            is Either.Right -> return this.halt("At pop $l: ${r.d}")
                        }
                    }
                    st = st.normalize()
                }
                val succ = g.succ(it)
                /**
                 * If we reach the end of the function but our stack isn't in a good state,
                 * something sus is happening, bail out.
                 */
                if(succ.isEmpty()) {
                    if(it !in g.cache.revertBlocks && st.isErrorTrace()) {
                        return this.halt("Reached end of function in an error state, pops will not work $st")
                    }
                    return this.cont(listOf())
                }
                val nxt = mutableListOf<NBId>()
                for(s in g.succ(it)) {
                    /**
                     * this is a back jump, make sure we aren't diverging, i.e., ensure the state we are propagating back
                     * doesn't change the abstraction of the state at the head of the loop.
                     */
                    if(g.cache.domination.dominates(s, it)) {
                        val loopHeadState = getBlockStartState(s).leftOrNull() ?: return this.halt("could not get state at loop head $s")
                        if(loopHeadState != st) {
                            return this.halt("At backjump from $it -> $s, stack mismatches: $st vs $loopHeadState")
                        }
                    } else {
                        nxt.add(s)
                    }
                }
                blockOut[it] = st
                return this.cont(nxt)
            }

            override fun reduce(results: List<Unit>): String? {
                return null
            }
        }
        val result = worker.submit(g.rootBlockIds)
        if(result != null) {
            logger.warn { "Failed to normalize exits in ${c.name}: $result" }
        }
        /**
         * Now, find cases where we need to start duplication, these are those blocks where we had a good state
         * coming out, but our successor does not have a good state coming in, indicating that going from Curr -> Succ
         * is where the mismatch begins.
         */
        val toWork = g.blockIds.filterToSet { b ->
            blockOut[b]?.isErrorTrace() == false && g.succ(b).any { succ ->
                succ !in g.cache.revertBlocks && blockIn[succ]?.isErrorTrace() == true
            }
        }
        if(toWork.isEmpty()) {
            return c
        }
        val patch = c.toPatchingProgram()

        for(start in toWork) {
            /**
             * Start with our good state.
             */
            val st = blockOut[start]!!
            if(st.isErrorTrace()) {
                logger.warn {
                    "In ${c.name}, thought we had a sane starting stack at $start, but we do not"
                }
                continue
            }
            /**
             * Remappers are not shared, because each mismatch sees its own new version of the path.
             */
            val remapper = BlockRemapper(
                patcher = patch,
                g = g,
                blockIn = blockIn.build()
            )

            /**
             * Rewrite the successors of this block.
             */
            val succs = g.succ(start).associateWith {
                remapper.getCloneOrOrig(it)
            }
            val last = g.elab(start).commands.last()
            val replaced = if(PatchingTACProgram.SIMPLE.isJumpCommand(last.cmd)) {
                PatchingTACProgram.SIMPLE.remapSuccessors(last.cmd) {
                    succs[it]!!
                }
            } else {
                last.cmd
            }
            val succSet = succs.values.toTreapSet()
            patch.replaceCommand(last.ptr, listOf(replaced), succSet)
            /**
             * Then duplicate the path out of this block until we reach a good state
             */
            val err = worklist(remapper, st[treapListOf()]!!, succSet, patcher = patch, graph = g)
            if(err != null) {
                logger.warn {
                    "Error rewriting $start in ${c.name}: $err"
                }
                // we have to return here because we may have a partially rewritten program, there is no way to
                // roll those back
                return c
            }
        }
        /**
         * At this point, all of the blocks which were involved in an error trace aren't reachable from the root, so
         * they need to be removed!
         */
        blockIn.keysMatching { _, t ->
            t.isErrorTrace()
        }.let(patch::removeBlocks)

        return patch.toCode(c)
    }

    /**
     * Iteratively explore the program starting [succ] until we reach points with a good stack. Note that we start
     * this process in a single stack [initState], because we start the iteration from a point in the program where we
     * have a single, principle stack.
     * Returns a non-null string on error.
     */
    private fun worklist(mapper: BlockRemapper, initState: PersistentStack<Int>, succ: TreapSet<NBId>, patcher: SimplePatchingProgram, graph: TACCommandGraph) : String? {
        /**
         * state sanity represents the expected "good" state along this path. In other words, it gives the stack we
         * expect to see after doing this duplication.
         */
        val stateSanity = succ.associateWith { initState }.toMutableMap()
        var worklist = succ
        /**
         * for not rewriting blocks twice
         */
        val visited = mutableSetOf<NBId>()
        val nxt = treapSetBuilderOf<NBId>()
        while(worklist.isNotEmpty()) {
            for(w in worklist) {
                // if w is not in newBlocks, this is a good path, no need to remap
                val origBlock = mapper.newBlocks[w] ?: continue

                // already rewrote this block
                if(!visited.add(w)) {
                    continue
                }
                val st = stateSanity[w] ?: return "No stack found at $w despite being reachable from duplication path"
                /**
                 * Handle block returns the successor blocks we saw, and the state of the stack after stepping the block.
                 */
                val (nextState, succs) = handleBlock(
                    graph = graph,
                    remapper = mapper,
                    patcher = patcher,
                    inState = st,
                    newBlock = w,
                    origBlock = origBlock
                )
                for(s in succs) {
                    nxt.add(s)
                    val curr = stateSanity[s]
                    if(curr != null && curr != nextState) {
                        return "disagreement at $s about what the stack should be after duplication"
                    }
                    stateSanity[s] = nextState
                }
            }
            worklist = nxt.build()
            nxt.clear()
        }
        return null
    }

    /**
     * A class which handles the logic of deciding whether a block needs to be cloned or if the original block
     * can be used. Roughly, revert blocks are never cloned, otherwise we clone a block if its in state
     * is an error trace (indicating this block still "sees" a mismatch).
     *
     * a key-value (k, v) in [newBlocks] records for each each new block id `k` the original block `v` it clooes.
     * [remapped] is the reverse, a key value (k,v) records for each original block `k` the cloned block id `v`.
     */
    private class BlockRemapper(val patcher: SimplePatchingProgram, val blockIn: TreapMap<NBId, StackTrace>, val g: TACCommandGraph) {
        val remapped = mutableMapOf<NBId, NBId>()
        val newBlocks = treapMapBuilderOf<NBId, NBId>()
        fun getCloneOrOrig(b: NBId) : NBId {
            if(b in g.cache.revertBlocks) {
                return b
            }
            if(blockIn[b]?.isErrorTrace() != true) {
                return b
            }
            return remapped.getOrPut(b) {
                patcher.createOpenBlockFrom(b).also {
                    newBlocks[it] = b
                }
            }
        }
    }

    /**
     * Clones block [origBlock] into [newBlock], erasing [INTERNAL_FUNC_EXIT] annotations that are not relevant
     * for the stack in [inState]. From the correctness of the analysis we know that, along this path with the irrelevant
     * pop annotations erased, we *will* eventually reach a coherent stack state.
     */
    private fun handleBlock(
        remapper: BlockRemapper,
        newBlock: NBId,
        origBlock: NBId,
        patcher: SimplePatchingProgram,
        graph: TACCommandGraph,
        inState: PersistentStack<Int>
    ) : Pair<PersistentStack<Int>, TreapSet<NBId>> {
        val clonedContents = mutableListOf<TACCmd.Simple>()
        val origCommands = graph.elab(origBlock).commands

        /**
         * Find the successors of this block, either original or cloned (as handled by the [BlockRemapper]
         */
        val remappedSucc = graph.succ(origBlock).associateWith {
            remapper.getCloneOrOrig(it)
        }
        var st = inState

        for(lc in origCommands) {
            if(lc.ptr.pos == origCommands.lastIndex) {
                if(PatchingTACProgram.SIMPLE.isJumpCommand(lc.cmd)) {
                    clonedContents.add(PatchingTACProgram.SIMPLE.remapSuccessors(lc.cmd) {s ->
                        remappedSucc[s] ?: s
                    })
                    continue
                }
            }
            val annot = lc.maybeAnnotation(INTERNAL_FUNC_EXIT)
            /**
             * Not an exit command? who cares? keep it.
             */
            if(annot == null) {
                clonedContents.add(lc.cmd)
                continue
            }
            /**
             * If this is an irrelevant stack pop, skip it!
             */
            if(st.topOrNull() != annot.id) {
                clonedContents.add(TACCmd.Simple.NopCmd)
                continue
            }
            /**
             * otherwise, this is relevant to this path of execution, so update our stack accordingly.
             */
            clonedContents.add(lc.cmd)
            st = st.pop()
        }
        /**
         * Our new block is done, fill in the contents for this [newBlock]
         */
        val succSet = remappedSucc.values.toTreapSet()
        patcher.populateBlock(newBlock, clonedContents, succSet)
        /**
         * Return our state after stepping this block, and the successor blocks, which may be
         * some combination or original/cloned block ids.
         */
        return st to succSet
    }
}
