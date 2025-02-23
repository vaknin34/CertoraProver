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

package analysis.alloc

import analysis.CmdPointer
import analysis.LTACCmd
import analysis.TACBlock
import analysis.TACCommandGraph
import analysis.numeric.*
import analysis.pta.LoopCopyAnalysis
import analysis.worklist.IWorklistScheduler
import analysis.worklist.NaturalBlockScheduler
import analysis.worklist.StatefulWorklistIteration
import analysis.worklist.StepResult
import com.certora.collect.*
import evm.MAX_EVM_UINT256
import log.Logger
import log.LoggerTypes
import tac.NBId
import utils.containsAny
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACKeyword
import vc.data.TACSymbol
import java.math.BigInteger

private val logger = Logger(LoggerTypes.ALLOC)

enum class UseSort {
    MemWrite,
    MemRead,
    Value,
    Escape,
    Unsafe
}

private interface MayMustSets {
    fun toMaySet(): Set<TACSymbol.Var>
    fun toMustSet(): Set<TACSymbol.Var>
}

private sealed class ByteAllocDF : MayMustSets {
    data class S(val maySet: Set<TACSymbol.Var>, val mustSet: Set<TACSymbol.Var>) : ByteAllocDF() {
        override fun join(other: ByteAllocDF): ByteAllocDF =
                when(other) {
                    EMPTY -> S(this.maySet, emptySet())
                    is S -> if(this.maySet === other.maySet && this.mustSet === other.mustSet) { this } else {
                        S(this.maySet.union(other.maySet), this.mustSet.intersect(other.mustSet))
                    }
                }

        override fun toMaySet(): Set<TACSymbol.Var> = this.maySet
        override fun toMustSet(): Set<TACSymbol.Var> = this.mustSet
        override fun kill(k: TACSymbol.Var): ByteAllocDF =
                if(k !in maySet && k !in mustSet) {
                    this
                } else if(k in maySet && k in mustSet && mustSet.size == 1 && maySet.size == 1) {
                    EMPTY
                } else {
                    S(this.maySet.minus(k), this.mustSet.minus(k))
                }

        override fun plus(k: TACSymbol.Var): ByteAllocDF = S(this.maySet.plus(k), this.mustSet.plus(k))
    }

    object EMPTY : ByteAllocDF() {
        override fun join(other: ByteAllocDF): ByteAllocDF = when(other) {
            EMPTY -> this
            else -> other.join(this)
        }
        override fun toMaySet(): Set<TACSymbol.Var> = setOf()
        override fun toMustSet(): Set<TACSymbol.Var> = setOf()
        override fun kill(k: TACSymbol.Var): ByteAllocDF = this

        override fun plus(k: TACSymbol.Var): ByteAllocDF = S(setOf(k), setOf(k))

        override fun toString(): String = "EMPTY"
    }

    abstract fun join(other: ByteAllocDF) : ByteAllocDF
    abstract fun kill(k: TACSymbol.Var) : ByteAllocDF
    abstract fun plus(k: TACSymbol.Var) : ByteAllocDF
}


private data class State(val pointerDf: ByteAllocDF, val num: TreapMap<TACSymbol.Var, IntValue>) : MayMustSets by pointerDf {
    fun join(other: State) : State {
        return State(pointerDf.join(other.pointerDf), num.join(other.num, IntValue.Nondet))
    }

    fun widen(next: State) : State {
        return State(pointerDf.join(next.pointerDf), this.num.widen(next.num, IntValue.Nondet))
    }
}


open class FreePointerAnalysis(private val graph: TACCommandGraph) {
    private val numericSemantics = object : SimpleIntervalAbstractInterpreter<TreapMap<TACSymbol.Var, IntValue>>(
            expressionInterpreter = SimpleIntervalExpressionSemantics(SimpleIntervalValueSemantics)
    ) {
        override fun project(l: LTACCmd, w: TreapMap<TACSymbol.Var, IntValue>): TreapMap<TACSymbol.Var, IntValue> = w
    }


    open fun stop(where: LTACCmd) = false
    open fun record(where: LTACCmd) = false
    open fun isViolation(maySet: Set<TACSymbol>, where: LTACCmd) = false

    open fun skipStatement(ltac: LTACCmd) : Boolean = false

    fun doMayMustAnalysis(
            readLocations: Set<CmdPointer>,
            readOffset: Map<CmdPointer, BigInteger> = mapOf()
    ) : Map<CmdPointer, Pair<Set<TACSymbol.Var>, Set<TACSymbol.Var>>>? {
        val state = mutableMapOf<NBId, State>()
        val joinCount = mutableMapOf<NBId, Int>()
        val dom = graph.cache.domination
        val starts = readLocations.map { it.block }.toSet().let { startNodes ->
            startNodes.filter { x ->
                startNodes.none { y ->
                    x != y && dom.dominates(y, x)
                }
            }
        }
        starts.forEach { state.put(it, State(ByteAllocDF.EMPTY, treapMapOf())) }
        logger.info {
            "Starting at block $starts"
        }

        fun propagate(v: NBId, p: State): Boolean {
            if(v !in state) {
                state[v] = p
                return true
            }
            val curr = state[v]!!
            val confNum = joinCount.compute(v) { _, mapped ->
                mapped?.plus(1) ?: 1
            }!!
            val join = if(confNum > 3) { curr.widen(p) } else { curr.join(p) }
            state[v] = join
            return join != curr
        }

        val result = mutableMapOf<CmdPointer, State>()

        val res = object : StatefulWorklistIteration<NBId, Boolean, Boolean>() {
            override val scheduler: IWorklistScheduler<NBId> = NaturalBlockScheduler(graph)

            override fun reduce(results: List<Boolean>): Boolean {
                return results.none {
                    !it
                }
            }

            override fun process(it: NBId): StepResult<NBId, Boolean, Boolean> {
                var itState = state[it]!!
                val lBlock = graph.elab(it)
                logger.trace {
                    "At reached $lBlock in state:\n$itState"
                }
                for(lcmd in lBlock.commands) {
                    if (this@FreePointerAnalysis.skipStatement(lcmd)) {
                        continue
                    }
                    if (this@FreePointerAnalysis.stop(lcmd)) {
                        logger.trace { "At $lcmd, stopping" }
                        result.merge(lcmd.ptr, itState) { a, b ->
                            a.join(b)
                        }
                        return this.result(true)
                    }
                    if (this@FreePointerAnalysis.isViolation(itState.toMaySet(), lcmd)) {
                        logger.trace { "At $lcmd, found violation" }
                        return this.halt(false)
                    }
                    val usage = if (lcmd.ptr in readLocations) {
                        UseSort.Value
                    } else {
                        classifyUse(lcmd, itState.toMaySet(), itState.toMustSet(), itState.num)
                    }
                    logger.trace { "At $lcmd, free pointer usage is $usage" }
                    val killed = if (lcmd.cmd is TACCmd.Simple.AssigningCmd) {
                        itState.pointerDf.kill(lcmd.cmd.lhs)
                    } else {
                        itState.pointerDf
                    }
                    logger.trace { "At $lcmd, the kill set is $killed" }
                    val num_ = numericSemantics.step(lcmd, itState.num).let { steppedNum ->
                        if (lcmd.ptr in readLocations && lcmd.cmd is TACCmd.Simple.AssigningCmd) {
                            logger.trace { "At $lcmd, we have the offset ${readOffset[lcmd.ptr] ?: BigInteger.ZERO}" }
                            val offset = readOffset[lcmd.ptr] ?: BigInteger.ZERO
                            steppedNum + (lcmd.cmd.lhs to IntValue.Constant(offset))
                        } else {
                            steppedNum
                        }
                    }.let {
                        val rhs = lcmd.cmd.getFreeVarsOfRhs()
                        if (lcmd.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd &&
                                lcmd.cmd.rhs is TACExpr.Vec.Add &&
                                rhs.containsAny(itState.toMustSet()) && it[lcmd.cmd.lhs]?.x == IntValue.Nondet) {
                            logger.debug {
                                "Attempting post-hoc cleanup on overflow on pointer at $lcmd"
                            }
                            // assume no overflow when adding to pointers (not necessarily sound, but a pretty good assumption)
                            val newLb = lcmd.cmd.getRhs().map {
                                when (it) {
                                    is TACSymbol.Const -> it.value
                                    is TACSymbol.Var -> itState.num[it]?.getLowerBound() ?: BigInteger.ZERO
                                }
                            }.fold(BigInteger.ZERO, BigInteger::add)
                            if (newLb > MAX_UINT) {
                                it
                            } else {
                                it + (lcmd.cmd.lhs to IntValue.Interval(newLb))
                            }
                        } else {
                            it
                        }
                    }
                    if (usage == null) {
                        itState = State(killed, num_)
                        continue
                    }
                    val plus = when (usage) {
                        UseSort.Value -> {
                            check(lcmd.cmd is TACCmd.Simple.AssigningCmd)
                            killed.plus(lcmd.cmd.lhs)
                        }
                        UseSort.MemRead,
                        UseSort.MemWrite -> killed
                        else -> {
                            logger.warn { "Found an unsafe usage at $lcmd with usage $usage our state $itState" }
                            return this.halt(false)
                        }
                    }
                    itState = State(plus, num_)
                }
                return propagateToNext(lBlock, itState)
            }

            private fun propagateToNext(lcmd: TACBlock, st: State): StepResult<NBId, Boolean, Boolean> {
                val lastCmd = lcmd.commands.last()
                val succPointers =
                        if (lastCmd.cmd is TACCmd.Simple.SummaryCmd && lastCmd.cmd.summ is LoopCopyAnalysis.LoopCopySummary) {
                                setOf(lastCmd.cmd.summ.originalBlockStart)
                        } else {
                            graph.succ(lcmd.id)
                        }
                return this.cont(succPointers.filter { propagate(it, st) })
            }
        }.submit(starts)
        if(!res) {
            return null
        }
        return result.mapValues {
            it.value.toMaySet() to it.value.toMustSet()
        }
    }

    companion object {

        fun isOpaqueEVMOp(lc: LTACCmd): Boolean {
            return (
                    lc.cmd is TACCmd.Simple.CallCore ||
                            lc.cmd is TACCmd.Simple.ReturnCmd ||
                            lc.cmd is TACCmd.Simple.ReturnSymCmd ||
                            lc.cmd is TACCmd.Simple.RevertCmd ||
                            lc.cmd is TACCmd.Simple.LogCmd
                    )
        }


        fun classifyUse(lc: LTACCmd, may: Collection<TACSymbol.Var>, must: Collection<TACSymbol.Var>, num: Map<TACSymbol.Var, IntValue>) : UseSort? {
            if(isOpaqueEVMOp(lc)) {
                return null
            }
            if(lc.cmd is TACCmd.Simple.SummaryCmd || lc.cmd is TACCmd.Simple.AnnotationCmd) {
                return null
            }
            if(!may.containsAny(lc.cmd.getRhs())) {
                return null
            }
            if(lc.cmd is TACCmd.Simple.AssigningCmd.AssignSha3Cmd || lc.cmd is TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd) {
                return null
            }
            // otherwise
            return when(lc.cmd) {
                is TACCmd.Simple.AssigningCmd.ByteLoad -> {
                    assert(lc.cmd.loc in may)
                    UseSort.MemRead
                }
                is TACCmd.Simple.AssigningCmd.AssignExpCmd -> {
                    if(lc.cmd.rhs is TACExpr.BinExp &&
                            (lc.cmd.rhs is TACExpr.BinOp.Sub || lc.cmd.rhs is TACExpr.BinRel) &&
                            lc.cmd.rhs.o1AsTACSymbol() in must &&
                            lc.cmd.rhs.o2AsTACSymbol() in must) {
                        null
                    } else if(
                            lc.cmd.rhs is TACExpr.BinOp.Sub &&
                            lc.cmd.rhs.o1AsTACSymbol() in must &&
                            (lc.cmd.rhs.o2AsTACSymbol() in num || lc.cmd.rhs.o2AsTACSymbol() is TACSymbol.Const)) {
                        val boundApprox = num[lc.cmd.rhs.o1AsTACSymbol() as TACSymbol.Var]!!
                        val lb = when (val o2 = lc.cmd.rhs.o2AsTACSymbol()) {
                            is TACSymbol.Var -> num[o2] ?: IntValue.Nondet
                            is TACSymbol.Const -> IntValue.Constant(o2.value)
                        }
                        if (lb.x.getUpperBound() <= boundApprox.x.getLowerBound()) {
                            UseSort.Value
                        } else {
                            UseSort.Unsafe
                        }
                    /* WEIRD right?
                       Well, as it turns out, we need to handle this bizarre pattern that appears when copying a string out
                       of call data during a write. Fun times.
                     */
                    } else if(lc.cmd.rhs is TACExpr.BinRel.Gt && lc.cmd.rhs.operandsAreSyms() && lc.cmd.rhs.o1AsTACSymbol() in must &&
                            lc.cmd.rhs.o2AsTACSymbol().let {sym ->
                                (sym is TACSymbol.Const && sym.value == BigInteger("ffffffffffffffff", 16)) ||
                                        (sym is TACSymbol.Var && num[sym]?.takeIf {
                                            it.isConstant
                                        }?.let {
                                            it.c == BigInteger("ffffffffffffffff", 16)
                                        } == true)
                            }) {
                        null
                    } else if(lc.cmd.rhs is TACExpr.BinRel && lc.cmd.rhs.operandsAreSyms() && lc.cmd.rhs.o1AsTACSymbol() in must && lc.cmd.rhs.o2AsTACSymbol() in must) {
                        null
                    } else if(lc.cmd.rhs is TACExpr.Sym || lc.cmd.rhs is TACExpr.Vec.Add) {
                        UseSort.Value
                    } else if (lc.cmd.rhs is TACExpr.BinRel.Eq && lc.cmd.rhs.o2 is TACExpr.Select && lc.cmd.rhs.o2.baseAsTACSymbolVar() == TACKeyword.MEMORY.toVar() && lc.cmd.rhs.o2.locAsTACSymbol() in must) {
                        null
                    } else if (lc.cmd.rhs is TACExpr.BinOp.BWAnd && lc.cmd.rhs.operandsAreSyms()) {
                        val operands = listOf((lc.cmd.rhs.o1 as TACExpr.Sym).s, (lc.cmd.rhs.o2 as TACExpr.Sym).s)
                        if(operands.any {
                            it is TACSymbol.Const && it.value == MAX_EVM_UINT256.andNot(31.toBigInteger())
                            } && operands.any {
                                it is TACSymbol.Var && it in must && num[it]?.isDefinitelyGreaterThan(30.toBigInteger()) == true
                            }) {
                            UseSort.Value
                        } else {
                            UseSort.Unsafe
                        }
                    } else {
                        UseSort.Unsafe
                    }
                }
                is TACCmd.Simple.AssigningCmd.ByteStore -> {
                    if(lc.cmd.value in may) {
                        return UseSort.Escape
                    } else {
                        assert(lc.cmd.loc in may)
                        UseSort.MemWrite
                    }
                }
                is TACCmd.Simple.AssigningCmd.ByteStoreSingle -> {
                    if(lc.cmd.value in may) {
                        UseSort.Escape
                    } else {
                        assert(lc.cmd.loc in may)
                        UseSort.MemWrite
                    }
                }
                is TACCmd.Simple.ByteLongCopy -> {
                    if(lc.cmd.dstBase != TACKeyword.MEMORY.toVar()) {
                        null
                    } else if(lc.cmd.dstOffset in may) {
                        UseSort.MemWrite
                    } else {
                        UseSort.Unsafe
                    }
                }
                is TACCmd.Simple.WordStore -> {
                    if(lc.cmd.value in may) {
                        UseSort.Escape
                    } else {
                        // super weird, but not unsafe per se
                        UseSort.Value
                    }
                }
                // catch all for "dunno, not willing to say it's safe"
                else -> UseSort.Unsafe
            }
        }
    }
}
