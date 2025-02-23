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

package optimizer

import analysis.enarrow
import analysis.narrow
import tac.Tag
import vc.data.*
import java.math.BigInteger


object BitwiseOptimizer {
    /**
     * XOR optimization. c = a xor b, d = c > 0; ==> d = a != b
     */
    fun xorOptimize(c: CoreTACProgram): CoreTACProgram {
        val patch = c.toPatchingProgram()
        val g = c.analysisCache.graph
        val use = c.analysisCache.use
        g.commands.mapNotNull { xorCmdMaybe ->
            if (xorCmdMaybe.cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd || xorCmdMaybe.cmd.rhs !is TACExpr.BinOp.BWXOr) {
                return@mapNotNull null
            }
            val uses = use.useSitesAfter(xorCmdMaybe.cmd.lhs, xorCmdMaybe.ptr)
            uses.singleOrNull()?.let {
                g.elab(it).let { u ->
                    if (u.cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd
                        || u.cmd.rhs !is TACExpr.BinRel.Gt
                        || u.cmd.rhs.o1 !is TACExpr.Sym.Var
                        || u.cmd.rhs.o1.s != xorCmdMaybe.cmd.lhs
                        || u.cmd.rhs.o2 !is TACExpr.Sym.Const
                        || u.cmd.rhs.o2.s.value != BigInteger.ZERO
                    ) {
                        return@mapNotNull null
                    }
                    xorCmdMaybe.enarrow<TACExpr.BinOp.BWXOr>() to u.narrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()
                }
            }
        }.forEach { (xorCmd, useXor) ->
            val tmp = TACKeyword.TMP(Tag.Bool, "xorReplace")
            patch.addVarDecl(tmp)
            patch.replaceCommand(useXor.ptr, listOf(TACCmd.Simple.NopCmd))
            // if the only use of the xor use is in a jumpi, we can swap the jumpi
            val useOfUse = use.useSitesAfter(useXor.cmd.lhs, useXor.ptr).singleOrNull()?.let { g.elab(it) }
            if (useOfUse == null || useOfUse.cmd !is TACCmd.Simple.JumpiCmd) {
                patch.replaceCommand(
                    xorCmd.ptr, listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            tmp,
                            TACExpr.BinRel.Eq(xorCmd.exp.o1, xorCmd.exp.o2)
                        ),
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            useXor.cmd.lhs,
                            TACExpr.UnaryExp.LNot(tmp.asSym())
                        )
                    )
                )
            } else {
                patch.replaceCommand(
                    xorCmd.ptr, listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            useXor.cmd.lhs,
                            TACExpr.BinRel.Eq(xorCmd.exp.o1, xorCmd.exp.o2)
                        )
                    )
                )
                patch.update(
                    useOfUse.ptr
                ) { jump ->
                    (jump as TACCmd.Simple.JumpiCmd).copy(
                        dst = jump.elseDst,
                        elseDst = jump.dst
                    )
                }
            }
        }
        return patch.toCode(c)
    }
}