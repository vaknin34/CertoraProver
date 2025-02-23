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

package analysis.icfg

import analysis.CmdPointer
import analysis.LTACCmd
import analysis.LTACCmdView
import analysis.icfg.CalleeAnalysis.WorkContinuation.*
import analysis.narrow
import analysis.numeric.AbstractAbstractInterpreter
import analysis.numeric.DelegatingSemantics
import analysis.numeric.IPathSemantics
import analysis.numeric.IStatementInterpreter
import analysis.opt.numeric.*
import analysis.opt.VROIntMap
import analysis.worklist.IWorklistScheduler
import analysis.worklist.MonadicStatefulParallelWorklistIteration
import analysis.worklist.ParallelStepResult
import com.certora.collect.*
import datastructures.stdcollections.*
import evm.MASK_SIZE
import log.*
import tac.NBId
import utils.`to?`
import utils.uniqueOrNull
import vc.data.*
import java.math.BigInteger

private typealias CalleeState = VROIntMap

private val logger = Logger(LoggerTypes.INLINER)

/**
 * Forward call resolution analysis based on the [VROInt] abstraction and semantics.
 * This analysis does *not* track information necessary towards proving math operations correct, focusing instead on symbolic
 * must/must-not equals information. At call-sites with unresolved callees, the sets of variables known to be equal to the callee
 * variable are consulted, and if a contract address symbol exists in that set, we set the call-site's callee equal to that
 * address.
 */
object CalleeAnalysis {
    private val pathSem = object : SaturatingVROPathSemantics<CalleeState>() {
        override fun assignVar(toStep: CalleeState, lhs: TACSymbol.Var, toWrite: VROInt, where: LTACCmd): CalleeState {
            return toStep + (lhs to toWrite)
        }

    }

    private val capture = VROIntMap::plus

    private val expressionInterpreter = object : VROExpressionInterpreter<CalleeState>(object : DelegatingSemantics<CalleeState, VROInt, Any>(VROBaseValueSemantics) {
        override fun evalBWAnd(
            v1: VROInt,
            o1: TACSymbol,
            v2: VROInt,
            o2: TACSymbol,
            toStep: CalleeState,
            input: CalleeState,
            whole: Any,
            l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
        ): VROInt {
            val del = super.evalBWAnd(v1, o1, v2, o2, toStep, input, whole, l)
            var extraQuals = treapListOf<VROQuals>()

            /**
             * If we know that one of the operands is the address mask, and the other operand is an address,
             * then we know that this bwand is a nop (we could likely get this not from the qualifiers
             * but from the integer bounds, but whatever).
             */
            fun checkAddressSaturation(
                maybeMask: VROInt,
                maybeAddress: TACSymbol
            ) {
                if(maybeMask.x.isConstant && maybeMask.x.c == MASK_SIZE(160) && maybeAddress is TACSymbol.Var) {
                    if(toStep.saturate(o2).any {
                            it is TACSymbol.Var && TACMeta.CONTRACT_ADDR_KEY in it.meta
                        }) {
                        extraQuals = extraQuals.add(VROQuals.MustEqual(maybeAddress))
                    }
                }
            }

            checkAddressSaturation(v1, o2)
            checkAddressSaturation(v2, o1)
            if(extraQuals.isEmpty()) {
                return del
            }
            return del.withQualifiers(del.qual + extraQuals)
        }
    }) {
        @Suppress("EXTENSION_SHADOWED_BY_MEMBER")
        override fun CalleeState.plus(entry: Pair<TACSymbol.Var, VROInt>): CalleeState {
            return capture(this, entry)
        }
    }

    private val stmtInterp = object : VROStatementInterpreter<CalleeState>(
        expressionInterpreter, pathSem
    ) {
        override fun forget(
            lhs: TACSymbol.Var,
            toStep: CalleeState,
            input: CalleeState,
            whole: Any,
            l: LTACCmd
        ): CalleeState {
            return toStep.forget(lhs)
        }

        @Suppress("EXTENSION_SHADOWED_BY_MEMBER")
        override fun CalleeState.plus(entry: Pair<TACSymbol.Var, VROInt>): CalleeState {
            return capture(this, entry)
        }
    }

    private val interpreter = object : AbstractAbstractInterpreter<CalleeState, CalleeState>() {
        override val statementInterpreter: IStatementInterpreter<CalleeState, CalleeState> = stmtInterp
        override val pathSemantics: IPathSemantics<CalleeState, CalleeState> = pathSem

        override fun project(l: LTACCmd, w: CalleeState): CalleeState {
            return w
        }

        override fun killLHS(
            lhs: TACSymbol.Var,
            s: CalleeState,
            w: CalleeState,
            narrow: LTACCmdView<TACCmd.Simple.AssigningCmd>
        ): CalleeState {
            return s.kill(lhs)
        }

        override fun postStep(stepped: CalleeState, l: LTACCmd): CalleeState {
            return stepped
        }
    }

    /**
     * continuation for items generated by the worklist. [Next] populates the worklist if the join yields
     * a new state, [CallResolution] and [JumpResolution] update the "global" jump state.
     */
    private sealed class WorkContinuation {
        data class Next(val where: NBId, val state: CalleeState) : WorkContinuation()
        data class CallResolution(val where: CmdPointer, val which: TreapSet<TACSymbol>) : WorkContinuation()
        data class JumpResolution(val where: CmdPointer, val which: Boolean?) : WorkContinuation()
    }

    fun resolveCallees(ctp: CoreTACProgram) : CoreTACProgram {
        val callResolution = mutableMapOf<CmdPointer, TreapSet<TACSymbol>>()
        val jumpResolution = mutableMapOf<CmdPointer, Boolean>()

        val state = mutableMapOf(ctp.entryBlockId to CalleeState())
        val graph = ctp.analysisCache.graph
        object : MonadicStatefulParallelWorklistIteration<NBId, WorkContinuation, Unit, Unit>(null) {
            override val scheduler: IWorklistScheduler<NBId> = ctp.analysisCache.naturalBlockScheduler

            override fun commit(c: WorkContinuation, nxt: MutableCollection<NBId>, res: MutableCollection<Unit>) {
                when(c) {
                    /**
                     * From the assumed monotonicity of the jump resolution and call resolution we don't bother with
                     * a join here, and just overwrite the previous value.
                     */
                    is WorkContinuation.CallResolution -> {
                        callResolution[c.where] = c.which
                    }
                    is WorkContinuation.JumpResolution -> {
                        if(c.which == null) {
                            jumpResolution.remove(c.where)
                        } else {
                            jumpResolution[c.where] = c.which
                        }
                    }
                    is WorkContinuation.Next -> {
                        if(c.where !in state) {
                            state[c.where] = c.state
                            nxt.add(c.where)
                        } else {
                            val prev = state[c.where]
                            val joined = prev!!.intersect(c.state) { _, v1, v2 -> v1.join(v2) }
                            if(prev != joined) {
                                state[c.where] = joined
                            }
                            nxt.add(c.where)
                        }
                    }
                }
            }

            override fun reduce(results: List<Unit>) {

            }

            override fun process(it: NBId): ParallelStepResult<WorkContinuation, Unit, Unit> {
                val start = state[it] ?: error("Internal error, hit block without an entry, how?")
                var stateIter = start
                val block = graph.elab(it)
                val cont = mutableListOf<WorkContinuation>()
                for(lc in block.commands) {
                    if(lc.cmd is TACCmd.Simple.JumpiCmd && lc.cmd.cond is TACSymbol.Var) {
                        val av = stateIter[lc.cmd.cond]
                        var resolution : Boolean? = null
                        if(av != null) {
                            if(av.x.mustNotEqual(BigInteger.ZERO)) {
                                resolution = true
                            } else if(av.x.mustEqual(BigInteger.ZERO)) {
                                resolution = false
                            }
                        }
                        cont.add(WorkContinuation.JumpResolution(lc.ptr, resolution))
                    /**
                     * Is this a call-site with an unresolved callee address? if so, save the variables we found.
                     */
                    } else if(lc.cmd is TACCmd.Simple.SummaryCmd && lc.cmd.summ is CallSummary && lc.cmd.summ.callTarget.any { it !is CallGraphBuilder.CalledContract.FullyResolved.ConstantAddress}) {
                        cont.add(WorkContinuation.CallResolution(lc.ptr, stateIter.saturate(lc.cmd.summ.toVar).toTreapSet()))
                    }
                    val nxt = interpreter.step(lc, stateIter)
                    stateIter = nxt
                }
                graph.pathConditionsOf(it).entries.mapNotNull { (k, v) ->
                    k `to?` interpreter.propagate(
                        l = block.commands.last(), w = stateIter, pathCondition = v
                    )
                }.filter { (which, st) ->
                    which !in state || state[which]!! != st
                }.forEach { (blk, st) ->
                    cont.add(WorkContinuation.Next(blk, st))
                }
                return ParallelStepResult.ContinueWith(cont = cont)
            }
        }.submit(listOf(ctp.entryBlockId))

        /**
         * Find those call-sites where there is a unique contract address variable, and record that
         * instance id.
         */
        val resolvedReferences = callResolution.mapNotNull { (ptr, v) ->
            ptr `to?` v.mapNotNull {
                (it as? TACSymbol.Var)?.meta?.find(TACMeta.CONTRACT_ADDR_KEY)
            }.uniqueOrNull()
        }

        if(jumpResolution.isEmpty() && resolvedReferences.isEmpty()) {
            return ctp
        }

        return ctp.patching { p ->
            /**
             * Prune the graph with static information (scary!)
             */
            p.selectConditionalEdges(jumpResolution.map {
                graph.elab(it.key).narrow<TACCmd.Simple.JumpiCmd>() to it.value
            }, explicitlyAssumeTheSelection = true)

            /**
             * Resolve the callees.
             */
            resolvedReferences.forEach { (where, addr) ->
                val orig = graph.elab(where).narrow<TACCmd.Simple.SummaryCmd>()
                val summ = orig.cmd.summ as CallSummary
                logger.info {
                    "In ${ctp.name} @ $summ, resolved symbolic to concrete address $addr"
                }
                val updated = summ.copy(
                    callTarget = setOf(CallGraphBuilder.CalledContract.FullyResolved.ConstantAddress(
                        contractId = addr
                    ))
                )
                p.replaceCommand(where, listOf(orig.cmd.copy(
                    summ = updated
                )))
            }
        }
    }
}
