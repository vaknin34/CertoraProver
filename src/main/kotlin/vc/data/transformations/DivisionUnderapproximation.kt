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

package vc.data.transformations

import analysis.maybeNarrow
import config.Config
import log.*
import tac.Tag
import utils.`to?`
import vc.data.*

/**
 * Implements two underapproximations for divisions:
 * 1. Constant dividers - changes all divisions to a constant divider as specified in [Config.DivideByConstants].
 * 2. No remainder in div - sets all divisions to have no remainders - enabled if [Config.DivideNoRemainder] is true.
 * If none of [Config.DivideByConstants] or [Config.DivideNoRemainder] are set, will return the original program [p].
 */
object DivisionUnderapproximation {
    fun doWork(p: CoreTACProgram): CoreTACProgram {
        if (Config.DivideByConstants.getOrNull() == null && !Config.DivideNoRemainder.get()) {
            return p
        }

        // rewrite all divisions to use the constant
        val patch = p.toPatchingProgram()
        val divCmds = p.analysisCache.graph.commands
            .mapNotNull {
                it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()
                    ?.takeIf { it.cmd.rhs is TACExpr.BinOp.Div || it.cmd.rhs is TACExpr.BinOp.IntDiv }
                    ?.let { lcmd ->
                        lcmd `to?` (lcmd.cmd.rhs as TACExpr.BinOp).o2
                    }.takeIf { it?.second !is TACExpr.Sym.Const }
            }

        divCmds.forEach { (divCmd, _) ->
            val errorMsg = "Got invalid expression in ${divCmd.cmd}@${divCmd.ptr}"
            val divExp = divCmd.cmd.rhs as? TACExpr.BinOp ?: throw IllegalStateException(errorMsg)
            val replacement = mutableListOf<TACCmd.Simple>()
            val src = divCmd.cmd.metaSrcInfo?.getSourceCode() ?: "(No source)"

            if (Config.DivideByConstants.getOrNull() != null) {
                Logger.regression { "Applying div by constant $src" }
                val divider = Config.DivideByConstants.get().asTACSymbol().asSym()
                val newDivCmd = when (divExp) {
                    is TACExpr.BinOp.Div -> divCmd.cmd.copy(rhs = divExp.copy(o2 = divider))
                    is TACExpr.BinOp.IntDiv -> divCmd.cmd.copy(rhs = divExp.copy(o2 = divider))
                    else -> throw IllegalStateException(errorMsg)
                }
                replacement.add(newDivCmd)
            }

            if (Config.DivideNoRemainder.get()) {
                Logger.regression { "Applying div no remainders $src" }
                val tmp = TACKeyword.TMP(Tag.Bool, "divNoRemainder")
                patch.addVarDecl(tmp)
                replacement.add(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    tmp,
                    TACExpr.BinRel.Eq(
                        TACExpr.Vec.IntMul(divCmd.cmd.lhs.asSym(), divExp.o2),
                        divExp.o1
                    )
                ))
                replacement.add(TACCmd.Simple.AssumeCmd(tmp))
            }
            patch.replaceCommand(
                divCmd.ptr,
                replacement
            )
        }

        return patch.toCode(p)
    }
}
