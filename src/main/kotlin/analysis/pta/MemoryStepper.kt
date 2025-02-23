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

package analysis.pta

import analysis.CmdPointer
import analysis.LTACCmd
import analysis.LTACCmdView
import analysis.alloc.AllocationAnalysis
import analysis.narrow
import log.*
import vc.data.*
import vc.data.tacexprutil.subsFull
import vc.data.tacexprutil.toSymSet
import java.math.BigInteger

private val logger = Logger(LoggerTypes.ABSTRACT_INTERPRETATION)

private fun containsSubExpr(e: TACExpr) = !(
    e is TACExpr.Sym || e.getOperands().all { it is TACExpr.Sym }
    )

abstract class MemoryStepper<S, R>(val scratchSite: Set<CmdPointer>,
                                   val allocSites: Map<CmdPointer, AllocationAnalysis.AbstractLocation>) {

    fun step(ltacCmd: LTACCmd, pState: S) : R {
        val seed : R = extract(pState)
        val kill = if(ltacCmd.cmd is TACCmd.Simple.AssigningCmd) {
            this.killLhsRelations(ltacCmd.cmd.lhs, seed, pState, ltacCmd)
        } else {
            seed
        }
        return when(ltacCmd.cmd) {
            is TACCmd.Simple.AssigningCmd -> {
                when (ltacCmd.cmd) {
                    is TACCmd.Simple.AssigningCmd.ByteStore -> {
                        if (ltacCmd.cmd.base == TACKeyword.MEMORY.toVar()) {
                            writeMemory(ltacCmd.cmd.loc, ltacCmd.cmd.value, kill, pState, ltacCmd)
                        } else {
                            logger.info { "ignoring byte write to unrelated (?) variable ${ltacCmd.cmd.base} @ ${ltacCmd.ptr}" }
                            kill
                        }
                    }
                    is TACCmd.Simple.AssigningCmd.ByteStoreSingle -> {
                        if (ltacCmd.cmd.base == TACKeyword.MEMORY.toVar()) {
                            writeSingleMemory(ltacCmd.cmd.loc, ltacCmd.cmd.value, kill, pState, ltacCmd)
                        } else {
                            logger.info { "ignoring byte write to unrelated (?) variable ${ltacCmd.cmd.base} @ ${ltacCmd.ptr}" }
                            kill
                        }
                    }
                    is TACCmd.Simple.AssigningCmd.ByteLoad -> {
                        if (ltacCmd.cmd.base == TACKeyword.MEMORY.toVar()) {
                            readMemory(ltacCmd.cmd.lhs, ltacCmd.cmd.loc, kill, pState, ltacCmd)
                        } else {
                            assignUninterpExpr(ltacCmd.cmd.lhs, ltacCmd.cmd.getRhs(), kill, pState, ltacCmd)
                        }
                    }

                    is TACCmd.Simple.AssigningCmd.WordLoad -> {
                        handleWordLoad(ltacCmd.narrow(), kill, pState)
                    }
                    is TACCmd.Simple.AssigningCmd.AssignHavocCmd -> {
                        assignNondetInt(ltacCmd.cmd.lhs, kill, pState, ltacCmd)
                    }
                    is TACCmd.Simple.AssigningCmd.AssignExpCmd -> {
                        val rhs: TACExpr = ltacCmd.cmd.rhs
                        if(containsSubExpr(rhs)) {
                            return assignUninterpExpr(
                                lhs = ltacCmd.cmd.lhs,
                                rhs = rhs.subsFull.toSymSet(),
                                where = ltacCmd,
                                target = kill,
                                pstate = pState
                            )
                        }
                        if(ltacCmd.cmd.usesVar(TACKeyword.MEM64.toVar()) && ltacCmd.cmd.rhs !is TACExpr.Sym) {
                            throw AnalysisFailureException("Found inlined use fo FP var $ltacCmd")
                        }
                        if(ltacCmd.cmd.lhs == TACKeyword.MEM64.toVar()) {
                            assignNondetInt(ltacCmd.cmd.lhs, where = ltacCmd, pstate = pState, target = kill)
                        } else {
                            when (rhs) {
                                is TACExpr.Sym -> {
                                    if (ltacCmd.ptr in scratchSite) {
                                        scratchAllocationTo(ltacCmd.cmd.lhs, kill, pState, ltacCmd)
                                    } else if (ltacCmd.ptr in allocSites) {
                                        val abstractLocation = allocSites[ltacCmd.ptr]!!
                                        allocationTo(ltacCmd.cmd.lhs, abstractLocation, kill, pState, ltacCmd)
                                    } else {
                                        when (val s = rhs.s) {
                                            is TACSymbol.Var -> {
                                                if (s == TACKeyword.MEM64.toVar()) {
                                                    throw AnalysisFailureException("Found unclassified use $ltacCmd")
                                                } else {
                                                    assignVariable(ltacCmd.cmd.lhs, s, kill, pState, ltacCmd)
                                                }
                                            }

                                            is TACSymbol.Const -> {
                                                assignConstant(ltacCmd.cmd.lhs, s.value, kill, pState, ltacCmd)
                                            }
                                        }

                                    }
                                }
                                is TACExpr.Vec.Add -> {
                                    assignAdd(ltacCmd.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), kill, pState, ltacCmd)
                                }
                                is TACExpr.BinRel.Lt -> {
                                    assignLt(ltacCmd.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), kill, pState, ltacCmd)
                                }
                                is TACExpr.Vec.Mul -> {
                                    assignMul(ltacCmd.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), kill, pState, ltacCmd)
                                }
                                is TACExpr.BinOp.ShiftLeft -> {
                                    assignShiftLeft(ltacCmd.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), kill, pState, ltacCmd)
                                }
                                is TACExpr.BinOp.BWOr -> {
                                    assignOr(ltacCmd.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), kill, pState, ltacCmd)
                                }
                                is TACExpr.BinOp.BWAnd -> {
                                    assignAnd(ltacCmd.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), kill, pState, ltacCmd)
                                }
                                is TACExpr.BinOp.Sub -> {
                                    assignSub(ltacCmd.cmd.lhs, rhs.o1AsTACSymbol(), rhs.o2AsTACSymbol(), kill, pState, ltacCmd)
                                }
                                else -> {
                                    assignExpr(ltacCmd.cmd.lhs, ltacCmd.cmd.rhs, kill, pState, ltacCmd)
                                }
                            }
                        }
                    }
                    else -> assignUninterpExpr(ltacCmd.cmd.lhs, ltacCmd.cmd.getRhs(), kill, pState, ltacCmd)
                }
            }

            is TACCmd.Simple.WordStore -> {
                handleUninterpWrite(ltacCmd.cmd.value, kill, pState, ltacCmd)
                kill
            }
            /*
            XXX(jtoman): Is this sound? Will this only lose precision or can we become unsound?
             */
            is TACCmd.Simple.AssumeCmd,
            is TACCmd.Simple.AssumeNotCmd,
            is TACCmd.Simple.AssumeExpCmd,
            is TACCmd.Simple.AssertCmd,
            TACCmd.Simple.NopCmd,
            is TACCmd.Simple.JumpdestCmd,
            is TACCmd.Simple.LogCmd,
            is TACCmd.Simple.LabelCmd,
            is TACCmd.Simple.JumpiCmd,
            is TACCmd.Simple.CallCore,
            is TACCmd.Simple.SummaryCmd,
            is TACCmd.Simple.JumpCmd,
            is TACCmd.Simple.ReturnCmd,
            is TACCmd.Simple.ReturnSymCmd,
            is TACCmd.Simple.RevertCmd -> {
                this.stepOther(ltacCmd, kill, pState)
            }

            is TACCmd.Simple.AnnotationCmd -> {
                this.stepAnnotation(
                    kill,
                    pState,
                    ltacCmd.narrow()
                )
            }

            is TACCmd.Simple.ByteLongCopy -> {
                if(ltacCmd.cmd.dstBase == TACKeyword.MEMORY.toVar()) {
                    handleByteCopy(ltacCmd.cmd.dstOffset, ltacCmd.cmd.length, kill, pState, ltacCmd)
                } else {
                    kill
                }
            }
        }
    }

    protected open fun stepOther(ltacCmd: LTACCmd, kill: R, pState: S): R {
        return kill
    }

    protected open fun stepAnnotation(kill: R, pState: S, narrow: LTACCmdView<TACCmd.Simple.AnnotationCmd>): R {
        return kill
    }

    protected open fun handleWordLoad(ltacCmd: LTACCmdView<TACCmd.Simple.AssigningCmd.WordLoad>, kill: R, pState: S): R {
        return assignNondetInt(ltacCmd.cmd.lhs, kill, pState, ltacCmd.wrapped)
    }

    abstract fun writeSingleMemory(loc: TACSymbol, value: TACSymbol, target: R, pState: S, ltacCmd: LTACCmd): R

    open protected fun assignExpr(lhs: TACSymbol.Var, rhs: TACExpr, target: R, pstate: S, ltacCmd: LTACCmd): R {
        return assignUninterpExpr(lhs, rhs.subsFull.toSymSet(), target, pstate, ltacCmd)
    }

    abstract fun handleUninterpWrite(value: TACSymbol, target: R, pState: S, ltacCmd: LTACCmd)

    abstract fun handleByteCopy(dstOffset: TACSymbol, length: TACSymbol, target: R, pState: S, ltacCmd: LTACCmd): R

    abstract fun readMemory(lhs: TACSymbol.Var, loc: TACSymbol, target: R, pState: S, ltacCmd: LTACCmd): R
    abstract fun writeMemory(loc: TACSymbol, value: TACSymbol, target: R, pState: S, ltacCmd: LTACCmd): R

    /**
      Model the assignment to the lhs a value derived from some (uninterpreted) operation over the set of symbols in [rhs]
     */
    abstract fun assignUninterpExpr(lhs: TACSymbol.Var, rhs: Set<TACSymbol>, target: R, pstate: S, where: LTACCmd) : R
    abstract fun assignShiftLeft(c: TACSymbol.Var, op1: TACSymbol, op2: TACSymbol, target: R, pstate: S, where: LTACCmd) : R
    abstract fun assignOr(c: TACSymbol.Var, op1: TACSymbol, op2: TACSymbol, target: R, pstate: S, where: LTACCmd) : R
    abstract fun assignAnd(c: TACSymbol.Var, op1: TACSymbol, op2: TACSymbol, target: R, pstate: S, where: LTACCmd) : R
    abstract fun assignSub(c: TACSymbol.Var, op1: TACSymbol, op2: TACSymbol, target: R, pstate: S, where: LTACCmd) : R
    abstract fun assignMul(c: TACSymbol.Var, op1: TACSymbol, op2: TACSymbol, target: R, pstate: S, where: LTACCmd) : R
    abstract fun assignLt(c: TACSymbol.Var, op1: TACSymbol, op2: TACSymbol, target: R, pstate: S, where: LTACCmd) : R
    abstract fun assignAdd(c: TACSymbol.Var, op1: TACSymbol, op2: TACSymbol, target: R, pstate: S, where: LTACCmd) : R

    abstract fun scratchAllocationTo(lhs: TACSymbol.Var, target: R, pstate: S, where: LTACCmd) : R
    abstract fun allocationTo(lhs: TACSymbol.Var, abstractLocation: AllocationAnalysis.AbstractLocation, target: R, pstate: S, where: LTACCmd) : R

    /**
     * Assign a non-deterministic integer to [lhs]. (The rhs hand side of this assignment is completely opaque)
     */
    abstract fun assignNondetInt(lhs: TACSymbol.Var, target: R, pstate: S, where: LTACCmd) : R
    abstract fun assignConstant(lhs: TACSymbol.Var, value: BigInteger, target: R, pstate: S, where: LTACCmd) : R
    abstract fun assignVariable(lhs: TACSymbol.Var, rhs: TACSymbol.Var, target: R, pstate: S, where: LTACCmd): R
    abstract fun killLhsRelations(lhs: TACSymbol.Var, init: R, pstate: S, where: LTACCmd): R

    abstract fun extract(pState: S): R
}
