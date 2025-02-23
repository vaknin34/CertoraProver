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

package analysis.icfg

import analysis.maybeExpr
import scene.IScene
import utils.mapNotNull
import vc.data.*
import datastructures.stdcollections.*

/**
 * Replaces calls to the [vc.data.TACBuiltInFunction.LinkContractAddress] with the symbolic variable name.
 * This code *strongly* assumes that invocations to this BIF are:
 * 1. only made with constant arguments, and
 * 2. Such constant arguments correspond to a contract *instance id*
 *
 * This is a safe assumption, as the only code that generates the LinkContractAddress BIF is our decompilation of the
 * synthetic opcode 0xe0, which always takes a constant argument.
 *
 */
object ContractLinker {
    fun linkContracts(c: CoreTACProgram, theScene: IScene) : CoreTACProgram {
        return c.parallelLtacStream().mapNotNull {
            it.maybeExpr<TACExpr.Apply>()?.takeIf {
                it.exp.f == TACBuiltInFunction.LinkContractAddress.toTACFunctionSym()
            }
        }.map {
            check(it.exp.ops.size == 1 && it.exp.ops[0] is TACExpr.Sym.Const) {
                "Something has gone terribly wrong, how did we get a non-constant contract id @ $it in ${c.name}"
            }
            it to (theScene.getContract((it.exp.ops[0] as TACExpr.Sym.Const).s.value).addressSym as TACSymbol)
        }.sequential().let { toRewrite ->
            c.patching { patcher ->
                toRewrite.forEach { (exp, libSymbol) ->
                    patcher.replaceCommand(exp.ptr, listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = exp.lhs,
                        rhs = libSymbol.asSym()
                    )))
                    (libSymbol as? TACSymbol.Var)?.let(patcher::addVarDecl)
                }
            }
        }
    }
}
