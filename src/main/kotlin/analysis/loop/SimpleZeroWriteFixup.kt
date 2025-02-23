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

package analysis.loop

import analysis.*
import analysis.smtblaster.*
import parallel.Parallel
import parallel.Scheduler
import parallel.bindFalseAsNull
import smtlibutils.data.SmtExp
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACKeyword
import vc.data.TACSymbol
import vc.data.tacexprutil.TACExprTransformer
import java.math.BigInteger
import datastructures.stdcollections.*

/**
 * Checks if the first memory write in a block stores zero
 */
class ZeroWriteChecker(graph: TACCommandGraph, private val blaster: IBlaster) : FixupBlockChecker {
    val builder: AbstractSmtExpTermBuilder = SmtExpIntTermBuilder
    private val constChecker = MustBeConstantAnalysis(wrapped = NonTrivialDefAnalysis(graph = graph, def = graph.cache.def), graph = graph)

    /**
     * Checks if [destBlock] contains a zero write to END.
     * @param scriptGen solver state, is not modified
     * @param destBlock the block to search
     * @param localState maps variables to their loop roles
     * @param localMapper is the transformer used to produce [localState]
     */
    override fun checkFixupBlock(
        scriptGen: Generator,
        destBlock: TACBlock,
        localState: MutableMap<TACSymbol.Var, TACExpr>,
        localMapper: TACExprTransformer<TACExpr>
    ): Parallel<FixupBlockResult?> {
        val writeCommand = destBlock.commands.firstOrNull {
            it.cmd is TACCmd.Simple.AssigningCmd.ByteStore && it.cmd.base == TACKeyword.MEMORY.toVar() && it.cmd.loc is TACSymbol.Var
        }?.narrow<TACCmd.Simple.AssigningCmd.ByteStore>() ?: return Scheduler.complete(null)
        /* Step up until that point, again, in terms of post loop values */
        for (i in 0 until writeCommand.ptr.pos) {
            if(destBlock.commands[i].cmd is TACCmd.Simple.AssigningCmd.ByteLoad) {
                return Scheduler.complete(null)
            }
            if (!stepSymbolic(localMapper, localState, destBlock.commands[i])) {
                return Scheduler.complete(null)
            }
        }
        /* Do we write 0? */
        if (constChecker.mustBeConstantAt(writeCommand.ptr, writeCommand.cmd.value) != BigInteger.ZERO) {
            val v = writeCommand.cmd.value
            if (v !is TACSymbol.Var) {
                return Scheduler.complete(null)
            }
            if (v !in localState) {
                return Scheduler.complete(null)
            }
            val expr = localState[v]!!
            if (!LogicalEquivalence.equiv(expr, TACSymbol.lift(0).asSym())) {
                return Scheduler.complete(null)
            }
        }
        val loc = writeCommand.cmd.loc as TACSymbol.Var
        if (loc !in localState) {
            return Scheduler.complete(null)
        }
        val finalWriteIdx = ExpressionTranslator(builder, List<SmtExp>::toTypedArray).blastExpr(localState[loc]!!, TACSymbol.Var::toSMTRep)
                ?: return Scheduler.complete(null)
        // now check the index, must it equal END?
        val finalWrite = scriptGen.bind { finalWrite ->
            finalWrite.assert {
                lnot(
                    eq(
                        toIdent(AbstractArraySummaryExtractor.LoopRole.END.name),
                        finalWriteIdx
                    )
                )
            }
            finalWrite.checkSat()
        }.build()
        return Scheduler.rpc { blaster.blastSmt(finalWrite.cmdList) }.bindFalseAsNull {
            Scheduler.complete(FixupBlockResult(
                fixupEnd = writeCommand.ptr,
                outputAccess = setOf(writeCommand.ptr),
                inputAccess = setOf()
            ))
        }
    }

}

/* Checks for a zero-write fixup after a copy loop */
class SimpleZeroWriteFixup(blaster: IBlaster, graph: TACCommandGraph) : CommonUnconditionalFixupReasoning(blaster, graph), FixupBlockChecker by ZeroWriteChecker(graph = graph, blaster = blaster)

/* Checks for a *conditional* zero-write fixup after a copy loop */
class ConditionalZeroWriteFixup(blaster: IBlaster, graph: TACCommandGraph) : CommonBranchingFixupReasoning(blaster, SmtExpIntTermBuilder, graph.cache.gvn), FixupBlockChecker by ZeroWriteChecker(graph, blaster)
