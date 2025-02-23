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

import analysis.icfg.ExpressionSimplifier
import analysis.narrow
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACKeyword
import vc.data.asTACSymbol
import java.math.BigInteger

/**
 * Converting [TACCmd.Simple.AssigningCmd.AssignSha3Cmd] to [TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd]
 */
object RawHashToSimpleHashConverter {

    fun convertRawHashToSimpleHash(code: CoreTACProgram): CoreTACProgram {
        val patch = code.toPatchingProgram()
        val g = code.analysisCache.graph
        val expSimplifier = ExpressionSimplifier(g, trySimplifyConfluence = true)
        g.commands.filter { it.cmd is TACCmd.Simple.AssigningCmd.ByteStore }.forEach {
            val mstoreCmd = it.narrow<TACCmd.Simple.AssigningCmd.ByteStore>()
            if (mstoreCmd.cmd.base == TACKeyword.MEMORY.toVar()) {
                val simplifiedLoc = expSimplifier.simplify(mstoreCmd.cmd.loc, it.ptr, true).getAsConst()
                when (simplifiedLoc) {
                    BigInteger.ZERO -> {
                        patch.addVarDecl(TACKeyword.MEM0.toVar())
                        patch.addBefore(it.ptr, listOf(
                                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                        TACKeyword.MEM0.toVar(),
                                        mstoreCmd.cmd.value,
                                        mstoreCmd.cmd.meta
                                )
                        ))
                    }
                    BigInteger.valueOf(32) -> {
                        patch.addVarDecl(TACKeyword.MEM32.toVar())
                        patch.addBefore(it.ptr, listOf(
                                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                                        TACKeyword.MEM32.toVar(),
                                        mstoreCmd.cmd.value,
                                        mstoreCmd.cmd.meta
                                )
                        ))
                    }
                }
            }
        }
        g.commands.filter { it.cmd is TACCmd.Simple.AssigningCmd.AssignSha3Cmd }.forEach { it ->
            val shaCmd = it.narrow<TACCmd.Simple.AssigningCmd.AssignSha3Cmd>()
            val simplifiedBase = expSimplifier.simplify(shaCmd.cmd.op1, it.ptr, true).getAsConst()
            val simplifiedSz = expSimplifier.simplify(shaCmd.cmd.op2, it.ptr, true).getAsConst()
            if (simplifiedBase == BigInteger.ZERO &&
                    (simplifiedSz == BigInteger.valueOf(32) ||
                            simplifiedSz == BigInteger.valueOf(64))) {
                val args = if (simplifiedSz == BigInteger.valueOf(32)) {
                    listOf(TACKeyword.MEM0.toVar())
                } else {
                    check(simplifiedSz == BigInteger.valueOf(64))
                    listOf(TACKeyword.MEM0.toVar(), TACKeyword.MEM32.toVar())
                }
                patch.addVarDecls(args.toSet())
                patch.replaceCommand(
                        it.ptr,
                        listOf(
                                TACCmd.Simple.AssigningCmd.AssignSimpleSha3Cmd(
                                        shaCmd.cmd.lhs,
                                        simplifiedSz!!.asTACSymbol(),
                                        args,
                                        shaCmd.cmd.meta
                                )
                        )
                )
            }

        }

        return patch.toCode(code)
    }
}
