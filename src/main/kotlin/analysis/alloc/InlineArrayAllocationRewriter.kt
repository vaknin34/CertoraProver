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

import allocator.Allocator
import analysis.*
import analysis.loop.AbstractArraySummaryExtractor
import analysis.loop.ArrayLoopSummarization
import analysis.loop.LoopSummarization
import analysis.smtblaster.SmtExpIntTermBuilder
import analysis.smtblaster.SmtExpScriptBuilder
import analysis.smtblaster.Z3BlasterPool
import analysis.worklist.StepResult
import analysis.worklist.VisitingWorklistIteration
import datastructures.stdcollections.*
import evm.EVM_ARRAY_ELEM_OFFSET
import parallel.*
import parallel.ParallelPool.Companion.runInherit
import tac.NBId
import tac.Tag
import utils.*
import vc.data.*
import java.math.BigInteger
import java.util.stream.Collectors
import java.util.stream.Stream

/**
  Finds free pointer assignments that are computed by a copy loop, replacing them with the equivalent expression format.

  For certain allocation patterns, the solidity compiler will use a loop variable as the value of a new free pointer.
  A (simplified) version of this pattern is:

  elem = base + 32
  it = 0
  while(it < len) {
     mem[elem + it] := ...
     it += 32
  }
  end = len + elem
  if(end % 32 == 0) {
     new_fp = end
  } else {
     // zero out copied junk
     new_fp = ... // end rounded up to nearest multiple of 32
  }
  fp = new_fp

  The allocation analysis just utterly falls over on this.

  This analysis recognizes an update of the free pointer where *one* of the reaching definitions is defined as e + l,
  where e is an element pointer for a preceding bytes array copy loop, and l is the length for that copy loop, i.e.,
  the true branch in the example above. It does not attempt to recognize the else case, and the rewrite triggers if we
  see the true branch (in that sense, this rewrite is fairly optimistic, in assuming the other branch doesn't utterly trash the free pointer).

  On a successful match, this analysis rewrites the update of the free pointer to:
  fp = elem + (len + 31 & ~31)

  which is the "standard" pattern for word-aligned allocations for bytes array.
 */
object InlineArrayAllocationRewriter {
    fun rewriteAllocations(p: CoreTACProgram) : CoreTACProgram {
        val graph = p.analysisCache.graph
        val arrayStartMatcher = PatternMatcher.compilePattern(graph, PatternDSL.build {
            (!TACKeyword.MEM64.toVar() + 0x20()).commute.withAction { _, _, _->
                true
            }
        })
        fun Loop.getFirst() = graph.elab(this.head).commands.first()
        val arrayPointerMatcher = object : SymbolQuery<Boolean> {
            override fun query(q: TACSymbol.Var, src: LTACCmd): Boolean {
                return graph.cache.gvn.equivBefore(src.ptr, q).contains(TACKeyword.MEM64.toVar())
            }

            override fun queryFrom(start: LTACCmdView<TACCmd.Simple.AssigningCmd>): Boolean {
                return start.cmd.lhs == TACKeyword.MEM64.toVar()
            }

        }
        val lengthMultMatcher = PatternMatcher.compilePattern(graph, PatternDSL.build {
            (0x20() * Var).commute.locSecond
        })
        val loops = getNaturalLoops(p.analysisCache.graph)
        val loopHeads = loops.mapToTreapSet {
            it.head
        }
        /*
          Find updates of the free pointer which are a single variable
         */
        val candidates = p.parallelLtacStream().filter {
            it.cmd is TACCmd.Simple.AssigningCmd && it.cmd.lhs == TACKeyword.MEM64.toVar() && it.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && it.cmd.rhs is TACExpr.Sym.Var
        }.map {
            it.enarrow<TACExpr.Sym.Var>()
        }.flatMap { fpWrite ->
            /*
             Scopes the search for end = len + elem to all predecessors that do not traverse a loop head.
             This is necessary to prevent failure in testPackedEncode in PointsToTest
             */
            val nonLoopPredecessors = object : VisitingWorklistIteration<NBId, NBId, Set<NBId>>() {
                override fun process(it: NBId): StepResult<NBId, NBId, Set<NBId>> {
                    val pred = graph.pred(it).filter {
                        it !in loopHeads
                    }
                    return StepResult.Ok(
                        result = listOf(it),
                        next = pred
                    )
                }

                override fun reduce(results: List<NBId>): Set<NBId> {
                    return results.toSet()
                }
            }.submit(listOf(fpWrite.ptr.block))
            val scopeDef = ScopedNonTrivialDefAnalysis(
                scope = nonLoopPredecessors,
                graph = graph,
                def = graph.cache.def
            )
            /*
              Where exactly one of the definition sites...
             */
            val x = scopeDef.nontrivialDef(fpWrite.exp.s, origin = fpWrite.ptr).singleOrNull { defPtr ->
                /*
                  Is defined as x + y and is *not* in the same block (this is to work around unconditional writes of 0 introduced
                  in solidity 8 which confuses this analysis)
                 */
                val defCmd = graph.elab(defPtr).cmd
                defCmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && defCmd.rhs is TACExpr.Vec.Add && defCmd.rhs.ls.all {
                    it is TACExpr.Sym.Var
                } && defPtr.block != fpWrite.ptr.block
            } ?: return@flatMap Stream.empty<Triple<ExprView<TACExpr.Sym.Var>, ExprView<TACExpr.Vec.Add>, Loop>>()
            /*
              Is the predecessor of this definition site a loop? If not, bail out
             */
            val predLoop = graph.pred(x.block).takeIf {
                it.size == 1
            }?.first()?.let { uniqueAddPred ->
                loops.singleOrNull { l ->
                    uniqueAddPred in l.body
                }
            } ?: return@flatMap Stream.empty<Triple<ExprView<TACExpr.Sym.Var>, ExprView<TACExpr.Vec.Add>, Loop>>()
            Stream.of(Triple(fpWrite, graph.elab(x).enarrow(), predLoop))
        }.collect(Collectors.toList())
        val dom by lazy {
            graph.cache.domination
        }
        infix fun CmdPointer.dominates(other: CmdPointer) = dom.dominates(this.block, other.block) && (this.block != other.block || this.pos < other.pos)
        val inlineWrite = ParallelPool.allocInScope(2000, {timeout -> Z3BlasterPool(z3TimeoutMs = timeout) }) { blaster ->
            val summarizer = LoopSummarization(loops = loops, g = graph, blaster = blaster)
            val arraySummarizer = object : ArrayLoopSummarization(z3Processor = blaster) {
                override fun couldBeDataSegmentSize(l: Loop, cand: TACSymbol.Var): Boolean {
                    return lengthMultMatcher.query(cand, l.getFirst()).toNullableResult() != null
                }

                override fun plausibleAssignment(l: Loop, v: TACSymbol.Var, r: LoopRole): Boolean {
                    return super.plausibleAssignment(l, v, r) && when (r) {
                        LoopRole.ELEM_START -> arrayStartMatcher.query(v, l.getFirst()).toNullableResult() ?: false
                        LoopRole.OBJ_POINTER -> arrayPointerMatcher.query(v, l.getFirst())
                        else -> true
                    }
                }
            }
            candidates.forkEveryOrNull { (writeLoc, addVals, loop) ->
                val loopSumm = summarizer.summarizeLoop(loop) ?: return@forkEveryOrNull null
                /*
                  The operands of the addition which gives (one of) the new values of the free pointer
                 */
                val ops = addVals.exp.ls.map {
                    (it as TACExpr.Sym.Var).s
                }
                /*
                  These variables are actually mutated by the loop, that's a no go
                 */
                if (ops.any {
                            it in loopSumm.iterationEffect && !loopSumm.iterationEffect[it].equivSym(it)
                        }) {
                    return@forkEveryOrNull null
                }
                /*
                 Is our predecessor loop a copy loop?
                 */
                arraySummarizer.isArrayWriteStride(summ = loopSumm).map {
                    it.singleOrNull()
                }.bindComposed { loopIt ->
                    /*
                       If it is a copy loop, but the variables of our addition aren't part of this loop, then stop here

                       NB: this is a little sensitive to meaningless temporary variables, so we're leaning of DSA a little bit here
                     */
                    if (ops.any {
                                it !in loopIt.roles
                            }) {
                        return@bindComposed null
                    }
                    /*
                      Check that the (symbolic) interpretation of the addition yields the symbolic end of the array.
                      In that case, we have a path where the free pointer is updated to be the end of a freshly copied
                      array
                     */
                    val script = SmtExpScriptBuilder(SmtExpIntTermBuilder)
                    AbstractArraySummaryExtractor.addAxioms(builder = script, sz = loopIt.assumedSize, elemStartOffset = EVM_ARRAY_ELEM_OFFSET)
                    script.assert {
                        lnot(
                                eq(
                                        toIdent(AbstractArraySummaryExtractor.LoopRole.END.name),
                                        plus(
                                                *ops.map {
                                                    toIdent(loopIt.roles[it]!!.name)
                                                }.toTypedArray()
                                        )
                                )
                        )
                    }
                    script.checkSat()
                    rpc {
                        blaster.blastSmt(script.cmdList)
                    }.bindFalseAsNull {
                        complete(Triple(addVals, loopIt, writeLoc))
                    }
                }
            }.pcompute().runInherit()
        }.filterNotNull().filter { (add, summ, sym) ->
            /*
              Ensure that the definition that reaches the addition is still live at the point the free pointer update occurs
             */
            add.exp.ls.map {
                (it as TACExpr.Sym.Var).s
            }.all {
                val def = graph.cache.def.defSitesOf(it, pointer = add.ptr)
                def.size == 1 && def.first().let { firstSite ->
                    firstSite dominates sym.ptr
                }
            /*
               ensure that the loop roles we have are sufficient to compute the new value of the free pointer
             */
            } && (summ.assumedSize != BigInteger.ONE || summ.roles.any {
                it.value == AbstractArraySummaryExtractor.LoopRole.LENGTH
            }) && (summ.roles.any {
                it.value == AbstractArraySummaryExtractor.LoopRole.LENGTH || it.value == AbstractArraySummaryExtractor.LoopRole.ELEM_LENGTH
            })
        }
        return p.patching {
            for((add, writeSumm, writeLoc) in inlineWrite) {
                if(writeSumm.assumedSize != BigInteger.ONE) {
                    continue
                }
                val cmds = mutableListOf<TACCmd.Simple>()
                val toWrite = run {
                    /*
                      Now do the rewrite
                     */
                    val lengthRole = writeSumm.roles.entries.find { roleKV ->
                        roleKV.value == AbstractArraySummaryExtractor.LoopRole.LENGTH
                    }!!.key
                    val add31Var = TACSymbol.Var(
                            "temp${Allocator.getFreshId(Allocator.Id.TEMP_VARIABLE)}",
                            Tag.Bit256
                    )
                    it.addVarDecl(add31Var)
                    cmds.add(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                    lhs = add31Var,
                                    rhs = TACExpr.Vec.Add(
                                            lengthRole.asSym(),
                                            31.toBigInteger().asTACSymbol().asSym()
                                    )
                            )
                    )
                    val maskBottomBits =
                            TACSymbol.Var(
                                    "temp${Allocator.getFreshId(Allocator.Id.TEMP_VARIABLE)}",
                                    Tag.Bit256
                            )
                    it.addVarDecl(maskBottomBits)
                    cmds.add(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                    lhs = maskBottomBits,
                                    rhs = TACExpr.BinOp.BWAnd(
                                            "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0".toBigInteger(16).asTACSymbol().asSym(),
                                            add31Var.asSym()
                                    )
                            )
                    )
                    val finalResult = TACSymbol.Var("temp${Allocator.getFreshId(Allocator.Id.TEMP_VARIABLE)}", Tag.Bit256)
                    it.addVarDecl(finalResult)
                    cmds.add(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                    lhs = finalResult,
                                    rhs = TACExpr.Vec.Add(
                                            add.exp.ls.filterNot { operand ->
                                                operand.equivSym(lengthRole)
                                            } + maskBottomBits.asSym()
                                    )
                            )
                    )
                    finalResult
                }
                it.replace(writeLoc.ptr) { cmd ->
                    cmds + listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                    lhs = TACKeyword.MEM64.toVar(),
                                    rhs = toWrite.asSym(),
                                    meta = cmd.meta + TACMeta.INLINE_ALLOC
                            )
                    )
                }
            }
        }

    }
}
