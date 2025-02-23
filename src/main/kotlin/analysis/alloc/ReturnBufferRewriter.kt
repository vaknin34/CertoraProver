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

import analysis.*
import utils.*
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACKeyword
import java.util.stream.Collectors
import java.util.stream.Stream

/*
  When solidity wants the return size, it will sometimes compute:

  v = (fp + RETURN_SIZE) - fp

  This is just a very specialized case of the ConstantComputationInliner pass.

  I HATE IT.
 */
object ReturnSizeCalculationSimplifer {
    private data class ReturnSizeCalc(
            val firstFpRead: CmdPointer,
            val secondFpRead: CmdPointer,
            val returnSizeRead: CmdPointer
    )

    private val returnDataBufferPatt = PatternDSL.build {
        val fpMatcher = Var { v, w ->
            if(v == TACKeyword.MEM64.toVar()) {
                PatternMatcher.VariableMatch.Match(w.ptr)
            } else {
                PatternMatcher.VariableMatch.Continue
            }
        }
        val returnSizeMatcher = Var { v, w ->
            if(v == TACKeyword.RETURN_SIZE.toVar()) {
                PatternMatcher.VariableMatch.Match(w.ptr)
            } else {
                PatternMatcher.VariableMatch.Continue
            }
        }
        ((fpMatcher + returnSizeMatcher) - fpMatcher).withAction { _: LTACCmd, (firstRead, returnRead), secondRead: CmdPointer ->
            ReturnSizeCalc(
                firstFpRead = firstRead,
                secondFpRead = secondRead,
                returnSizeRead = returnRead
            )
        }
    }

    fun rewriteReturnSizeCalc(p: CoreTACProgram) : CoreTACProgram {
        val graph = p.analysisCache.graph
        val bufMatcher = PatternMatcher.compilePattern(graph = graph, patt = returnDataBufferPatt)
        
        val toRewrite = p.code.entries.parallelStream().flatMap { (b, where) ->
            // quick short circuiting: skip blocks that either havoc return size, or do NOT touch tacM0x40
            if(where.none {
                        it is TACCmd.Simple.AssigningCmd && it.lhs == TACKeyword.MEM64.toVar()
                    } || where.any { it is TACCmd.Simple.AssigningCmd && it.lhs == TACKeyword.RETURN_SIZE.toVar() }) {
                return@flatMap Stream.empty<Pair<LTACCmd, ReturnSizeCalc>>()
            }
            where.mapIndexedNotNull { index, simple ->
                if(simple is TACCmd.Simple.AssigningCmd.AssignExpCmd && simple.rhs is TACExpr.BinOp.Sub) {
                    val ltac = LTACCmd(ptr = CmdPointer(b, index), cmd = simple)
                    bufMatcher.queryFrom(ltac.narrow()).toNullableResult()?.let {
                        ltac to it
                    }
                } else {
                    null
                }
            }.stream()
        }.filter { (_, b) ->
            b.firstFpRead.block == b.secondFpRead.block && b.returnSizeRead.block == b.firstFpRead.block
        }.filter { (_, b) ->
            b.firstFpRead == b.secondFpRead
        }.map { (l, _) ->
            l.narrow<TACCmd.Simple.AssigningCmd>()
        }.collect(Collectors.toList())
        if(toRewrite.isEmpty()) {
            return p
        }
        val patching = p.toPatchingProgram()
        for(r in toRewrite) {
            patching.replaceCommand(r.ptr, listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            lhs = r.cmd.lhs,
                            rhs = TACKeyword.RETURN_SIZE.toVar(),
                            meta = r.cmd.meta
                    )
            ))
        }
        return patching.toCode(p)
    }
}
