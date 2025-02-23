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

package analysis.dataflow

import analysis.CmdPointer
import analysis.LTACCmd
import analysis.TACCommandGraph
import analysis.worklist.SimpleWorklist
import com.certora.collect.*
import datastructures.stdcollections.*
import tac.NBId
import utils.intersectAll
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol

class OnDemandMustEqualsAnalysis(private val graph: TACCommandGraph) : IMustEqualsAnalysis {
    override fun equivAfter(cmd: CmdPointer, f: TACSymbol.Var) : Set<TACSymbol.Var> {
        val curr = graph.elab(cmd)
        if(curr.cmd is TACCmd.Simple.AssigningCmd && curr.cmd.lhs == f) {
            return if(curr.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && curr.cmd.rhs is TACExpr.Sym.Var) {
                    equivBefore(cmd, curr.cmd.rhs.s) + f
            } else {
                setOf(f)
            }
        }
        val before = equivBefore(cmd, f)
        if(curr.cmd is TACCmd.Simple.AssigningCmd && curr.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && curr.cmd.rhs is TACExpr.Sym.Var && curr.cmd.rhs.s in before) {
            return before + curr.cmd.lhs
        } else if(curr.cmd is TACCmd.Simple.AssigningCmd && curr.cmd.lhs in before) {
            return before - curr.cmd.lhs
        } else {
            return before
        }
    }

    private fun iterateForward(start: Collection<Pair<CmdPointer, TACSymbol.Var>>, target: CmdPointer, sym: TACSymbol.Var, visited: Set<NBId>): MutableList<TreapSet<TACSymbol.Var>> {
        val blockState = mutableMapOf<NBId, TreapMap.Builder<TACSymbol.Var, TreapSet<TACSymbol.Var>>>()
        val res = mutableListOf<TreapSet<TACSymbol.Var>>()
        val worklist = mutableListOf<NBId>()
        fun stepper(start: CmdPointer, state: TreapMap.Builder<TACSymbol.Var, TreapSet<TACSymbol.Var>>, nxt: MutableCollection<NBId>) {
            val block = graph.elab(start.block)
            val isResultStep = start.block == target.block && start.pos <= target.pos
            val stepUntil = if(isResultStep) {
                target.pos
            } else {
                block.commands.size
            }
            for(i in start.pos until stepUntil) {
                stepCommand(state, block.commands[i])
            }
            if(isResultStep && sym in state) {
                res.add(state[sym]!!)
            } else {
                for(i in stepUntil until block.commands.size) {
                    stepCommand(state, block.commands[i])
                }
                for(i in graph.succ(block.id)) {
                    if(i !in visited) {
                        continue
                    }
                    if(propagateNext(i, blockState, state)) {
                        nxt.add(i)
                    }
                }
            }
        }
        for((cmdStart, v) in start) {
            stepper(cmdStart, treapMapBuilderOf(v to treapSetOf(v)), worklist)
        }
        SimpleWorklist.iterateWorklist(worklist) { curr, nxt ->
            val st = blockState[curr]!!.build().builder()
            val block = graph.elab(curr)
            val startPtr = block.commands.first().ptr
            stepper(startPtr, st, nxt)
        }
        return res
    }

    private fun propagateNext(i: NBId, blockState: MutableMap<NBId, TreapMap.Builder<TACSymbol.Var, TreapSet<TACSymbol.Var>>>, state: TreapMap.Builder<TACSymbol.Var, TreapSet<TACSymbol.Var>>) : Boolean {
        val st = blockState.putIfAbsent(i, state)?.build()
        if (st == null) {
            return true
        } else {
            val newSt = st.merge(state) { k, a, b ->
                when {
                    a == null || b == null -> treapSetOf(k)
                    else -> a intersect b
                }
            }
            if (newSt != st) {
                blockState[i] = newSt.builder()
                return true
            }
        }
        return false
    }

    private fun findStartPoint(
            variable: TACSymbol.Var,
            beforeCmd: CmdPointer,
            visited: MutableSet<Pair<NBId, TACSymbol.Var>>,
            startBefore: MutableSet<Pair<CmdPointer, TACSymbol.Var>>
    ) {
        SimpleWorklist.iterateWorklist(listOf(beforeCmd to variable)) { (currPointer, v), nxt ->
            val block = graph.elab(currPointer.block)
            var pt = currPointer.pos
            var it = v
            while(pt > 0) {
                val lc = block.commands[pt - 1]
                if(lc.cmd is TACCmd.Simple.AssigningCmd && lc.cmd.lhs == it) {
                    if(lc.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && lc.cmd.rhs is TACExpr.Sym.Var) {
                        it = lc.cmd.rhs.s
                    } else {
                        startBefore.add(block.commands[pt].ptr to it)
                        return@iterateWorklist
                    }
                }
                pt--
            }
            val firstCmd = block.commands.first()
            val preds = graph.pred(firstCmd)
            if(preds.isEmpty()) {
                startBefore.add(firstCmd.ptr to it)
            } else {
                for(p in preds) {
                    val prevVar = if(p.cmd is TACCmd.Simple.AssigningCmd && p.cmd.lhs == it)  {
                        if(p.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && p.cmd.rhs is TACExpr.Sym.Var) {
                            p.cmd.rhs.s
                        } else {
                            startBefore.add(firstCmd.ptr to it)
                            continue
                        }
                    } else {
                        it
                    }
                    if((p.ptr.block to prevVar) in visited) {
                        return@iterateWorklist
                    }
                    visited.add(p.ptr.block to prevVar)
                    nxt.add(p.ptr to prevVar)
                }
            }
        }
    }

    override fun equivBefore(cmd: CmdPointer, f: TACSymbol.Var) : Set<TACSymbol.Var> {
        val startPoints = mutableSetOf<Pair<CmdPointer, TACSymbol.Var>>()
        val visited = mutableSetOf<Pair<NBId, TACSymbol.Var>>()
        findStartPoint(f, cmd, visited, startPoints)
        val bounds = visited.mapTo(mutableSetOf()) { it.first }
        bounds.add(cmd.block)
        val res = iterateForward(startPoints, target = cmd, sym = f, visited = bounds)
        if(res.isEmpty()) {
            return setOf(f)
        } else {
            val x = res.intersectAll()
            check (f in x)
            return x
        }
    }

    private fun stepCommand(st: MutableMap<TACSymbol.Var, TreapSet<TACSymbol.Var>>, lc: LTACCmd) {
        if(lc.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd &&
                lc.cmd.rhs is TACExpr.Sym.Var &&
                lc.cmd.rhs.s in st) {
            val newEquiv = st[lc.cmd.rhs.s]!! + lc.cmd.lhs
            for(i in newEquiv) {
                st[i] = newEquiv
            }
        } else if(lc.cmd is TACCmd.Simple.AssigningCmd && lc.cmd.lhs in st) {
            val equiv = st[lc.cmd.lhs]!!
            val newVal = equiv - lc.cmd.lhs
            for(i in equiv) {
                if(i == lc.cmd.lhs) {
                    continue
                }
                val oldVal = st.put(i, newVal)
                check(oldVal != null) { "ME step failed: $i must be in $st"}
                check(oldVal == equiv) { "ME step failed: $oldVal vs $equiv"}
            }
            st.remove(lc.cmd.lhs)
        }
    }
}