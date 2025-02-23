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

import datastructures.stdcollections.*
import analysis.numeric.*
import analysis.numeric.linear.*
import analysis.worklist.IWorklistScheduler
import analysis.worklist.NaturalBlockScheduler
import analysis.worklist.StatefulWorklistIteration
import analysis.worklist.StepResult
import com.certora.collect.*
import tac.NBId
import utils.*
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACKeyword
import vc.data.TACSymbol

/**
 * An interface to the linear invariants that hold on entry to each block
 */
data class GlobalInvariantAnalysisResult(
    private val graph: TACCommandGraph,
    private val invStartOfBlock: Map<NBId, LinearInvariants>,
    private val semantics: GlobalInvariantAnalysisSemantics
) {
    private val cache = mutableMapOf<CmdPointer, LinearInvariants>()

    /*
     * @return the [LinearInvariants] that hold before [loc] by stepping through
     *         the commands [loc.block] until [loc]
     */
    fun getBeforeLocation(loc: CmdPointer) : LinearInvariants {
        return cache.getOrPut(loc) {
            var inv = invStartOfBlock[loc.block].orEmpty()
            graph.elab(loc.block).commands.take(loc.pos).forEach {
                inv = semantics.step(it, inv)
            }
            inv
        }
    }
}

/**
 * A global analysis in the domain of [LinearInvariants], using a (subclass) of [GlobalInvariantAnalysisSemantics]
 * determined by [semantics]. The actual analysis is done in the [analyze] function.
 */
class GlobalInvariantAnalysis(private val semantics: GlobalInvariantAnalysisSemantics) {

    constructor(maxTerms: Int) : this(GlobalInvariantAnalysisSemantics(maxTerms))

    private inner class GlobalInvariantWorker(private val graph: TACCommandGraph) :
        StatefulWorklistIteration<NBId, Unit, GlobalInvariantAnalysisResult>() {

        override val scheduler: IWorklistScheduler<NBId> = NaturalBlockScheduler(graph)
        private val invStartOfBlock: MutableMap<NBId, LinearInvariants> = mutableMapOf()
        private val invEndOfBlock: MutableMap<NBId, LinearInvariants> = mutableMapOf()

        override fun reduce(results: List<Unit>): GlobalInvariantAnalysisResult = GlobalInvariantAnalysisResult(graph, invStartOfBlock.toMap(), semantics)

        override fun process(it: NBId): StepResult<NBId, Unit, GlobalInvariantAnalysisResult> {
            val invIntersectOfPreds = graph.pred(it).mapNotNull { blk -> invEndOfBlock[blk] }.reduceOrNull { acc: LinearInvariants, blk -> acc.fastJoin(blk) }.orEmpty()
            val cmds = graph.elab(it).commands
            var inv = semantics.startBlock(invIntersectOfPreds, graph.cache.lva.liveVariablesBefore(cmds.first().ptr).toTreapSet())
            invStartOfBlock[it] = inv
            cmds.forEach {
                inv = semantics.step(it, inv)
            }
            val newEndOfBlock = semantics.endBlock(inv)
            val scheduleSuccessors = newEndOfBlock != invEndOfBlock[it]
            invEndOfBlock[it] = newEndOfBlock
            if(scheduleSuccessors) {
                return this.cont(graph.succ(it))
            }
            return this.result(Unit)
        }
    }

    /**
     * Analyze the [graph] according to [semantics], producing a [GlobalInvariantAnalysisResult] which
     * itself exposes the set of linearinvariants that hold before each command point.
     */
    fun analyze(graph: TACCommandGraph): GlobalInvariantAnalysisResult {
        val w = GlobalInvariantWorker(graph)
        return w.submit(graph.rootBlocks.map { it.id })
    }
}

/**
 * An extendable interpreter for determining the set of [LinearInvariants] that hold at each point in the program. To be
 * used with the [GlobalInvariantAnalysis]
 */
open class GlobalInvariantAnalysisSemantics(private val maxTerms: Int) : AbstractAbstractInterpreter<LinearInvariants, LinearInvariants>() {

    open fun isRelevant(eq: LinearEquality) = true

    override val statementInterpreter: IStatementInterpreter<LinearInvariants, Any?>
        get() = object : AbstractStatementInterpreter<LinearInvariants, Any?>() {
            override fun forget(
                lhs: TACSymbol.Var,
                toStep: LinearInvariants,
                input: LinearInvariants,
                whole: Any?,
                l: LTACCmd
            ): LinearInvariants = toStep.kill(lhs)

            override fun stepExpression(
                lhs: TACSymbol.Var,
                rhs: TACExpr,
                toStep: LinearInvariants,
                input: LinearInvariants,
                whole: Any?,
                l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
            ): LinearInvariants {
                val cmd = l.cmd
                return if (cmd.lhs == TACKeyword.MEM64.toVar() || cmd.usesVar(TACKeyword.MEM64.toVar())) {
                    toStep
                } else {
                    fun LinearEquality.filter() = treapSetOfNotNull(this.takeIf { 
                        isRelevant(it) && it.term.size <= maxTerms 
                    })
                    fun TreapSet<LinearEquality>.filter() = this.retainAll { 
                        isRelevant(it) && it.term.size <= maxTerms 
                    }

                    val gen = treapSetOfNotNull(
                        LinearTerm.lift(cmd.rhs)?.takeIf {
                            it.terms.none { (v, _) ->
                                v is LVar.PVar && v.v == cmd.lhs
                            }
                        }?.let {
                            LinearEquality.build {
                                !cmd.lhs `=` it
                            }
                        }
                    )

                    toStep + input.genFor(cmd.lhs, rhs = cmd.rhs).filter() + gen.filter()
                }
            }
        }

    override val pathSemantics: IPathSemantics<LinearInvariants, LinearInvariants> = TrivialPathSemantics()

    override fun postStep(stepped: LinearInvariants, l: LTACCmd): LinearInvariants = stepped

    override fun killLHS(
        lhs: TACSymbol.Var,
        s: LinearInvariants,
        w: LinearInvariants,
        narrow: LTACCmdView<TACCmd.Simple.AssigningCmd>
    ): LinearInvariants = s.kill(lhs)

    override fun project(l: LTACCmd, w: LinearInvariants): LinearInvariants = w

    fun endBlock(invariants: LinearInvariants): LinearInvariants =
        invariants.updateElements { it.canonicalize() }

    fun startBlock(invariants: LinearInvariants, lva: TreapSet<TACSymbol.Var>): LinearInvariants =
        invariants.retainAll { it.relatesAny(lva) }
}
