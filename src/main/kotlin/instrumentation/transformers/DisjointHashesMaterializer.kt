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

package instrumentation.transformers

import analysis.CommandWithRequiredDecls
import analysis.maybeExpr
import analysis.merge
import datastructures.stdcollections.*
import scene.MethodAttribute
import scene.SceneIdentifiers
import tac.Tag
import utils.mapNotNull
import utils.`to?`
import vc.data.*
import java.util.stream.Collectors

object DisjointHashesMaterializer {
    fun materializeDisjointHashes(scene: SceneIdentifiers, program: CoreTACProgram): CoreTACProgram {
        val toInstr = program.parallelLtacStream().mapNotNull { cmd ->
            cmd.maybeExpr<TACExpr.Apply>()
        }.filter { expr ->
            /*
                      We are happy to assume that any application of this function will appear in a "top-level" assignment
                      because we only ever generate an application of this code *at* a top level assignment, and
                      any expression folding should not be folding in complex expressions (like a BIF application)
                     */
            (expr.exp.f as? TACExpr.TACFunctionSym.BuiltIn)?.bif == TACBuiltInFunction.DisjointSighashes &&
                expr.exp.ops.singleOrNull()?.getAsConst() != null
        }.mapNotNull { expr ->
            val addr = expr.exp.ops.single().getAsConst()!!
            expr `to?` scene.getContractOrNull(addr)?.getMethods()?.filter { methodIdentifiers ->
                methodIdentifiers.attribute == MethodAttribute.Common
            }?.mapNotNullTo(mutableSetOf()) { methodIdentifiers ->
                methodIdentifiers.sigHash?.n
            }
        }.map { (where, sigs) ->
            val lhs = where.cmd.lhs
            where.ptr to CommandWithRequiredDecls(
                listOf(
                    TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                        lhs = lhs
                    )
                ), lhs
            ).merge(sigs.map {
                val cmpId = TACKeyword.TMP(Tag.Bool, "!sighash").toUnique("!")
                CommandWithRequiredDecls(
                    listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            lhs = cmpId,
                            rhs = TACExpr.BinRel.Eq(
                                it.asTACSymbol().asSym(),
                                lhs.asSym()
                            )
                        ),
                        TACCmd.Simple.AssumeNotCmd(cmpId)
                    ), cmpId
                )
            }.let(CommandWithRequiredDecls.Companion::mergeMany))
        }.collect(Collectors.toList())
        return if (toInstr.isEmpty()) {
            program
        } else {
            program.patching { patch ->
                for ((where, ins) in toInstr) {
                    patch.replaceCommand(where, ins)
                }
            }
        }
    }
}
