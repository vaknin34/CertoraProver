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

package normalizer

import analysis.*
import normalizer.UnoptimizeFreeMem.doWork
import tac.Tag
import vc.data.*
import java.math.BigInteger


/**
 * Cancels the effects of optimization on reading from the free memory pointer.
 * See [doWork].
 */
object UnoptimizeFreeMem {
    data class FreeMemPlusConst(
        val use: CmdPointer,
        val c: BigInteger,
        val origFreeMemDef: CmdPointer
    )

    private val patt = PatternDSL.build {
        (Var { v, where ->
            if(v == freememPtr) { PatternMatcher.VariableMatch.Match(where) } else { PatternMatcher.VariableMatch.Continue }
        } + Const).commute.withAction { loc, fpRead, c0 -> FreeMemPlusConst(loc.ptr, c0, fpRead.ptr) }
    }

    private val freememPtr = TACKeyword.MEM64.toVar()

    /**
     * Offsets based on tacM0x40 should be based on the latest tacM0x40, not some early incarnation.
     * Performs the following:
     * Given:
     * x0 = tacM0x40
     * y = tacM0x40 + c1
     * tacM0x40 = y
     * x1 = x0 + c0
     *
     * the last assignment becomes:
     * x1 = tacM0x40 + c0 - c1
     */
    fun doWork(c: CoreTACProgram): CoreTACProgram {

        val g = c.analysisCache.graph
        val def = NonTrivialDefAnalysis(g)
        val matcher = PatternMatcher.compilePattern(g, patt)

        /**
         * Check that the free pointer at candidateToRewrite.use is defined as
         * fp := c + fp
         * where this assignment occurs *after* the read of the free pointer at candidateToRewrite.origFreeMemDef and
         * *before* the use site of candidateToRewrite.use. Further, there must be no intervening writes to the free pointer
         * between the definition site found and the read in [candidateToRewrite] (if there is, then we treat
         * the addition as pointer arithmetic for a previous allocation).
         *
         * If it does, return `c`, i.e., the amount the free pointer is incremented
         * between the free pointer read at origFreeMemDef and the addition at use.
         */
        fun findRewriteOffset(candidateToRewrite: FreeMemPlusConst): BigInteger? {
            val newFreeMemDef = def.nontrivialDefSingleOrNull(freememPtr, candidateToRewrite.use)
                ?.takeIf {
                    it.block == candidateToRewrite.use.block
                            && it.block == candidateToRewrite.origFreeMemDef.block
                            && candidateToRewrite.use.pos > it.pos && it.pos > candidateToRewrite.origFreeMemDef.pos &&
                            c.analysisCache.graph.iterateUntil(it).reversed().takeWhile {
                                it.ptr != candidateToRewrite.origFreeMemDef
                            }.none {
                                it.cmd is TACCmd.Simple.AssigningCmd && it.cmd.lhs == TACKeyword.MEM64.toVar()
                            }
                }?.let {
                    g.elab(it).maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()
                } ?: return null


            return matcher.queryFrom(newFreeMemDef).toNullableResult()?.c
        }

        val patch = c.toPatchingProgram()

        g.commands
            .filter { cmd -> cmd.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.cmd?.rhs is TACExpr.Vec.Add }
            .forEach { cmd ->
                matcher.queryFrom(cmd.narrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()).toNullableResult()?.let {
                    val rewriteC1 = findRewriteOffset(it)
                    if (rewriteC1 != null && it.c > rewriteC1) {
                        val lhs = g.elab(it.use).narrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>().cmd.lhs
                        val tmp = TACKeyword.TMP(Tag.Bit256,"freemem").toUnique()
                        patch.addVarDecl(tmp)
                        patch.replaceCommand(
                            it.use,
                            listOf(
                                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                    tmp,
                                    freememPtr.asSym()
                                ),
                                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                    lhs,
                                    TACExpr.Vec.Add(tmp.asSym(), (it.c - rewriteC1).asTACSymbol().asSym())
                                )
                            )
                        )
                    }
                }
            }

        return patch.toCode(c)
    }
}
