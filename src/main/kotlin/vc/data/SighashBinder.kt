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

package vc.data

import analysis.CommandWithRequiredDecls
import config.Config
import datastructures.stdcollections.*
import evm.DEFAULT_SIGHASH_SIZE
import evm.EVM_BITWIDTH256
import tac.MetaKey
import tac.MetaMap
import tac.Tag

class SighashBinder : OpcodeEnvironmentBinder {
    companion object {
        val SAFE_INSTRUMENTED_READ = MetaKey.Nothing("sighash.read.instrumentation")
    }
    override fun bindEnvironmentParam(cmd: TACCmd.EVM): Pair<TACSymbol.Var, CommandWithRequiredDecls<TACCmd.Simple>> {
        check(cmd is TACCmd.EVM.ExtCallCmd) {
            "Asked to bind the sighash for an evm command $cmd that is not a call command"
        }
        val output = TACKeyword.TMP(Tag.Bit256, "!sighash").toUnique("!")
        if(Config.EnableAggressiveABIOptimization.get()) {
            return output to CommandWithRequiredDecls(listOf(
                TACCmd.Simple.AssigningCmd.AssignHavocCmd(output)
            ), setOf(output))

        }
        val argSize = cmd.argsSize
        if(argSize is TACSymbol.Const && argSize.value < DEFAULT_SIGHASH_SIZE) {
            return output to CommandWithRequiredDecls(listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = output,
                    rhs = TACExpr.zeroExpr
                )
            ), setOf(output))
        }
        val readResult = TACKeyword.TMP(Tag.Bit256, "!raw").toUnique("!")
        val finalOutput = TACKeyword.TMP(Tag.Bit256, "!data").toUnique("!")
        val hasSighash = TACKeyword.TMP(Tag.Bool, "!hasSighash").toUnique("!")
        return output to CommandWithRequiredDecls(listOf(
            TACCmd.Simple.AssigningCmd.ByteLoad(
                lhs = readResult,
                base = cmd.memBaseMap,
                loc = cmd.argsOffset,
                meta = MetaMap(SAFE_INSTRUMENTED_READ)
            ),
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = output,
                rhs = TACExpr.BinOp.ShiftRightLogical(
                    o1 = readResult.asSym(),
                    o2 = (EVM_BITWIDTH256 - 32).asTACExpr
                )
            ),
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = hasSighash,
                rhs = TACExpr.BinRel.Ge(
                    o1 = argSize.asSym(),
                    o2 = DEFAULT_SIGHASH_SIZE.asTACExpr
                )
            ),
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = finalOutput,
                rhs = TACExpr.TernaryExp.Ite(
                    i = hasSighash.asSym(),
                    t = output.asSym(),
                    e = TACExpr.zeroExpr
                )
            )
        ), setOfNotNull(output, readResult, cmd.memBaseMap, cmd.argsOffset as? TACSymbol.Var, argSize as? TACSymbol.Var, finalOutput, hasSighash))
    }
}
