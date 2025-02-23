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

package analysis.skeyannotation

import analysis.*
import analysis.dataflow.IDefAnalysis
import analysis.dataflow.IUseAnalysis
import analysis.worklist.SimpleWorklist
import datastructures.ArrayHashMap
import datastructures.MutableNestedMap
import datastructures.mutableNestedMapOf
import datastructures.put
import datastructures.stdcollections.*
import tac.Tag
import vc.data.*
import vc.data.tacexprutil.QuantDefaultTACExprTransformerWithPointer

/** Represents a "dataflow source" of an expression. */
sealed class ExpWorkListItem {
    abstract val ptr: ExpPointer

    /** Represents a "dataflow source point" where the data does not come from a subexpression or from the rhs of an
     * assignment, but from somewhere else.
     * The concrete expressions which get their data in this way are:
     *  - variables (which get their value from assignments elsewhere in the program)
     *  - constants (which get their value via tac semantics) .*/
    data class ContextDataFlow(override val ptr: ExpPointer) : ExpWorkListItem()

    /** represents a data flow source point that is the right-hand side (rhs) of an assignment */
    data class AssignmentDataFlow(val assignmentCmdPtr: CmdPointer) : ExpWorkListItem() {
        override val ptr: ExpPointer = ExpPointer(assignmentCmdPtr, ExpPointer.Path(0))
    }

    /** Represents one "dataflow source point" of an expression with arguments. [prevIndex] denotes the index of the
     * argument. */
    data class IntraExpDataFlow(override val ptr: ExpPointer, val prevIndex: Int) : ExpWorkListItem()
}

/**
 * Data flows from inner expressions to outer expressions, from the rhs of an assignment to the lhs, and from the lhs
 * of an assignment to all the uses of that variable (according to an [IUseAnalysis]).
 *
 * So far we only support TACSimpleSimple, i.e., every [TACCmd.Simple.AssigningCmd] must be an
 * [TACCmd.Simple.AssigningCmd.AssignExpCmd], but it should be easy to add the other cases to [next] when needed.
 *
 * Backwards data flow is not implemented.
 *
 * (Analogous to [Direction] which is used in [BlockDataflowAnalysis].)
 */
sealed class ExpDirection {
    abstract fun next(graph: TACCommandGraph, src: ExpPointer): Collection<ExpWorkListItem>
    abstract fun prev(graph: TACCommandGraph, src: ExpPointer): Collection<ExpWorkListItem>
    abstract fun entry(graph: TACCommandGraph): Collection<ExpWorkListItem>

    object FORWARD : ExpDirection() {
        override fun next(graph: TACCommandGraph, src: ExpPointer): Collection<ExpWorkListItem> {
            return if (src.depth > 1) {
                setOf(ExpWorkListItem.IntraExpDataFlow(src.dropLast(), src.path.last()))
            } else {
                val ltacCmd = graph.elab(src.cmdPointer)
                when (val cmd = ltacCmd.cmd) {
                    is TACCmd.Simple.AssigningCmd -> {
                        check(
                            cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd ||
                                    cmd is TACCmd.Simple.AssigningCmd.AssignHavocCmd
                        )
                        {
                            "not in TacSimpleSimple form: $cmd -- would need to extend/modify the analysis to support " +
                                    "this.. "
                        }
                        val useAnalysis = graph.cache.use
                        val useSites = useAnalysis.useSitesAfter(cmd.lhs, src.cmdPointer)

                        when (src.path.list) {
                            listOf(0) -> {
                                useSites.flatMapTo(mutableSetOf()) { cmdPtr ->
                                    val useSiteLTacCmd = graph.elab(cmdPtr)
                                    when (useSiteLTacCmd.cmd) {
                                        is TACCmd.Simple.AnnotationCmd -> {
                                            // we don't deal with AnnotationCmds in this analysis; wouldn't know how to
                                            // apply the ExpPointer concept
                                            setOf()
                                        }
                                        is TACCmd.Simple.SummaryCmd -> {
                                            throw UnsupportedOperationException("summaries not yet supported at this point")
                                        }
                                        else -> {
                                            val ptrs = getExpPointersForVar(useSiteLTacCmd, cmd.lhs)
                                            check(ptrs.isNotEmpty())
                                            { "couldn't find var ${cmd.lhs} at its use site $useSiteLTacCmd" }
                                            ptrs.map { ExpWorkListItem.ContextDataFlow(it) }
                                        }
                                    }
                                }
                            }
                            listOf(1) -> {
                                // the assignment makes the rhs value flow to the lhs symbol
                                // (make this so the lhs variable also get an analysis result, basically, otherwise
                                //  we could ignore this case and just use the use analysis to go on)
                                listOf(ExpWorkListItem.AssignmentDataFlow(src.cmdPointer))
                            }
                            else -> error("unexpected path in AssignExpCmd: ${src.path} in $cmd.")

                        }

                    }
                    // we consider all non-assigning commands as sinks in a (forward) data flow sense:
                    else -> setOf()
                }
            }
        }

        override fun prev(graph: TACCommandGraph, src: ExpPointer): Collection<ExpWorkListItem> =
            throw UnsupportedOperationException("not yet implemented")

        override fun entry(graph: TACCommandGraph): Collection<ExpWorkListItem> =
            getDataflowSources(graph).map { ExpWorkListItem.ContextDataFlow(it) }
    }

    @Suppress("unused")
    object BACKWARD : ExpDirection() {
        override fun next(graph: TACCommandGraph, src: ExpPointer): Collection<ExpWorkListItem> =
            throw UnsupportedOperationException("not yet implemented")

        override fun prev(graph: TACCommandGraph, src: ExpPointer): Collection<ExpWorkListItem> =
            throw UnsupportedOperationException("not yet implemented")

        override fun entry(graph: TACCommandGraph): Collection<ExpWorkListItem> =
            throw UnsupportedOperationException("not yet implemented")
    }

    companion object {
        /**
         * Collect all "dataflow starting points", i.e., constants and variables that have no definition.
         */
        fun getDataflowSources(graph: TACCommandGraph): Set<ExpPointer> {
            val res = mutableSetOf<ExpPointer>()
            graph.commands.forEach { ltacCmd ->
                when (val cmd = ltacCmd.cmd) {
                    is TACCmd.Simple.AssigningCmd.AssignExpCmd -> {
                        res.addAll(
                            getDataflowSources(
                                ExpPointer.rhsOfAssign(ltacCmd.ptr),
                                cmd.rhs,
                                graph.cache.def
                            ).keys
                        )
                    }
                    is TACCmd.Simple.AssigningCmd.AssignHavocCmd -> {
                        res.add(ExpPointer.lhsOfAssign(ltacCmd.ptr))
                    }
                    else -> {}
                }
            }
            return res
        }

        /**
         * It's ok for [def] to be null iff we're looking for data sources with respect to single expression, rather
         * than a program, i.e., if we don't want to take assignments into account that may have happened earlier.
         */
        private fun getDataflowSources(
            base: ExpPointer,
            exp: TACExpr,
            def: IDefAnalysis? = null
        ): Map<ExpPointer, TACExpr> {
            val res = mutableMapOf<ExpPointer, TACExpr>()
            val tf = object : QuantDefaultTACExprTransformerWithPointer() {

                override fun transformConst(acc: QuantVarsAndExpPointer, exp: TACExpr.Sym.Const): TACExpr {
                    res[acc.expPointer] = exp
                    return super.transformConst(acc, exp)
                }

                override fun transformVar(acc: QuantVarsAndExpPointer, exp: TACExpr.Sym.Var): TACExpr {
                    if (exp.s !in acc.boundVars.quantifiedVars &&
                        def?.defSitesOf(exp.s, acc.expPointer.cmdPointer)?.isEmpty() != false
                    ) {
                        // a variable that has no def sites is a data flow source
                        res[acc.expPointer] = exp
                    }
                    return super.transformVar(acc, exp)
                }

                override fun transformStructConstant(
                    acc: QuantVarsAndExpPointer,
                    e: TACExpr.StructConstant,
                    tag: Tag?
                ): TACExpr {
                    // a [StructConstant] can be seen as an constant of struct sort
                    res[acc.expPointer] = e
                    return super.transformStructConstant(acc, e, tag)
                }
            }
            tf.transform(QuantDefaultTACExprTransformerWithPointer.QuantVarsAndExpPointer.getEmpty(base), exp)
            return res
        }


        private fun getPointersForVar(ltacCmd: LTACCmd, v: TACSymbol.Var): Set<ExpPointer> {
            return when (val cmd = ltacCmd.cmd) {
                is TACCmd.Simple.AssigningCmd -> {
                    check(cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd)
                    { "expecting TACSimpleSimple, got $cmd" }
                    // only look in the rhs for [AssigningCmd]s
                    val srcs = getDataflowSources(
                        ExpPointer.rhsOfAssign(ltacCmd.ptr),
                        cmd.rhs
                    )
                    srcs.filterValues { it is TACExpr.Sym.Var && it.s == v }.keys
                }
                else -> {
                    // look in all subExps, since this is not an assignment (these are data flow sinks -- we might
                    // optimize this away when using this for a forward data flow-based monotone analysis like skey
                    // propagation ... but it seems "canonical" to have it ...
                    cmd.exprs().flatMapIndexedTo(mutableSetOf()) { i, subExp ->
                        val srcs = getDataflowSources(
                            ExpPointer(ltacCmd.ptr, ExpPointer.Path(i)),
                            subExp
                        )
                        srcs.filterValues { it is TACExpr.Sym.Var && it.s == v }.keys
                    }
                }
            }
        }

        /**
         * Returns the occurrence positions of [lhs] in the given command [ltacCmd]
         */
        fun getExpPointersForVar(ltacCmd: LTACCmd, lhs: TACSymbol.Var): Collection<ExpPointer> {
            return getPointersForVar(ltacCmd, lhs)
        }
    }
}

/**
 * Abstract class for data flow analyses that can deal with nested expressions as they occur in TACSimpleSimple.
 * Follows [BlockDataflowAnalysis] as a model for the worklist-based fixpoint iteration.
 * See also [ExpDirection].
 *
 * Note: This implementation assumes TACSimpleSimple to some extent. In particular, the step function does not see
 * commands. (Would need to add a stepCmd, and also ExpDirection would need some extra cases.)
 */
abstract class ExpDataflowAnalysis<T : Any>(
    val graph: TACCommandGraph,
    private val lattice: JoinLattice<T>,
    val bottom: T,
    val direction: ExpDirection
) {

    private val debugMode = false // should be false when merging to master

    fun T.join(other: T): T = lattice.join(this, other)
    fun T.equiv(other: T): Boolean = lattice.equiv(this, other)

    private val varExpIn = mutableMapOf<ExpPointer, T>()
    private val innerExpIn = mutableMapOf<ExpPointer, MutableMap<Int, T>>()
    protected val expOut = ArrayHashMap<ExpPointer, T>()

    private val expOutPretty: MutableNestedMap<TACExpr, ExpPointer, T> = mutableNestedMapOf()

    /**
     * Provides a canonical handling of ite expressions to be used by inheritors, basically handling ite's like control
     * flow joins.
     * (This also means that the ite-expression itself is not needed for this operation; just the list of in-states, it
     * is assumed that the full three-element list is given.
     * Note this must be manually called by [stepExp] in order to be used.
     */
    protected fun handleIte(inState: List<T>): T {
        require(inState.size == 3) { "This method is meant to process the instates of an Ite -- but the " +
            "in-state list has size ${inState.size}" }
        return when (direction) {
            ExpDirection.FORWARD -> inState[1].join(inState[2])
            else -> throw UnsupportedOperationException("direction $direction not yet supported.")
        }
    }

    /** provides join for an arbitrary list to be used by inheritors */
    protected fun join(inState: List<T>) =
        inState.fold(bottom) { acc, t -> acc.join(t) }

    /**
     * in general terms, this computes abstractPost([inState], [exp])
     *
     * @param inState the incoming (intermediate) analysis results (aka abstract state)
     * @param exp the expression whose effect on the abstract state we're about to compute
     */
    abstract fun stepExp(inState: List<T>, exp: LTACExp): T

    /**
     * Defines to handle data flow from the left hand side of an assignment to the right hand side.
     * By default the analysis result passes unchanged.
     *
     * This method allows the analysis to handle assignments in the program in a specific manner.
     * */
    open fun stepAssignment(rhsState: T, assignment: LTACCmdView<TACCmd.Simple.AssigningCmd>): T = rhsState

    fun runAnalysis() {
        SimpleWorklist.iterateWorklist(direction.entry(graph).toList()) { item, workset ->
            if (item in workset) {
                workset.remove(item)
            }
            val expPointer = item.ptr
            // compute result at expression output from results at inputs
            val result = when (item) {
                is ExpWorkListItem.ContextDataFlow -> {
                    stepExp(listOf(varExpIn.computeIfAbsent(item.ptr) { bottom }), graph.elab(item.ptr))
                }
                is ExpWorkListItem.AssignmentDataFlow -> {
                    stepAssignment(varExpIn.computeIfAbsent(expPointer) { bottom }, graph.elab(item.assignmentCmdPtr).narrow())
                }
                is ExpWorkListItem.IntraExpDataFlow -> {
                    val exp = graph.elab(item.ptr)
                    val inDegree = exp.exp.getOperands().size
                    check(inDegree > 0)
                    { "not expecting an indegree of zero for an inner expression ($exp)" }
                    val start =
                        (0 until inDegree).map { i ->
                            innerExpIn.computeIfAbsent(item.ptr) {
                                mutableMapOf()
                            }.computeIfAbsent(i) {
                                bottom
                            }
                        }
                    stepExp(start, exp)
                }
            }

            // update and queue
            if (expOut[expPointer]?.equiv(result) != true) {
                expOut[expPointer] = result
                direction.next(graph, expPointer).forEach { nxt ->
                    when (nxt) {
                        is ExpWorkListItem.ContextDataFlow,
                        is ExpWorkListItem.AssignmentDataFlow -> {
                            if (nxt.ptr in varExpIn) {
                                val currStart = varExpIn[nxt.ptr]!!
                                val joinIn = currStart.join(result)
                                if (!joinIn.equiv(currStart)) {
                                    varExpIn[nxt.ptr] = joinIn
                                    workset.add(nxt)
                                }
                            } else {
                                varExpIn[nxt.ptr] = result
                                workset.add(nxt)
                            }
                        }
                        is ExpWorkListItem.IntraExpDataFlow -> {
                            if (nxt.ptr in innerExpIn &&
                                innerExpIn[nxt.ptr]?.containsKey(nxt.prevIndex) == true
                            ) {
                                val currStart = innerExpIn[nxt.ptr]!![nxt.prevIndex]!!
                                val joinIn = currStart.join(result)
                                if (!joinIn.equiv(currStart)) {
                                    innerExpIn[nxt.ptr]!![nxt.prevIndex] = joinIn
                                    workset.add(nxt)
                                }
                            } else {
                                innerExpIn.computeIfAbsent(nxt.ptr) { mutableMapOf() }[nxt.prevIndex] = result
                                workset.add(nxt)
                            }
                        }
                    }
                }
            }
        }
        if (debugMode) {
            expOut.entries.forEach { (ptr, res) -> expOutPretty.put(graph.elab(ptr).exp, ptr, res) }
        }
    }

}
