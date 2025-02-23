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

import vc.data.TACSymbol
import analysis.CmdPointer
import log.Logger
import log.LoggerTypes
import vc.data.CoreTACProgram
import vc.data.DefaultTACCmdMapper
import vc.data.TACCmd

private val logger = Logger(LoggerTypes.OPTIMIZE)
/**
 * As long as there are no loops, will ensure that X := OP(..., X, ...) cannot happen for X of primitive type
 */
object RecycledVarsRemover {
    fun noVarRecycle(code: CoreTACProgram): CoreTACProgram {
        val replacements = mutableMapOf<CmdPointer, TACCmd.Simple>()
        val g = code.analysisCache.graph
        val patch = code.toPatchingProgram()

        fun getCommandInPtr(p: CmdPointer) = replacements[p] ?: g.elab(p).cmd
        fun getUseSubstituteMapper(toReplace: TACSymbol.Var, replacement: TACSymbol.Var) =  object: DefaultTACCmdMapper() {
            init {
                patch.addVarDecl(replacement)
            }
            override fun mapVar(t: TACSymbol.Var): TACSymbol.Var {
                return if (t == toReplace) {
                    replacement
                } else {
                    t
                }
            }

            override fun mapLhs(t: TACSymbol.Var): TACSymbol.Var {
                return t // do not map lhs
            }
        }

        g.pointers.forEach { p ->
            val c = getCommandInPtr(p)
            if (c is TACCmd.Simple.AssigningCmd) {
                val lhs = c.lhs
                val rhs = c.getFreeVarsOfRhs()
                // only on primitives
                if (lhs.tag.isPrimitive() && lhs in rhs) {
                    // replace if lhs coincides with an rhs variable
                    val replaced = rhs.find { it == lhs }!!  // oof, equals ignores tag, get the one from the rhs
                    val replacement = replaced.toUnique("u")

                    logger.debug { "For def $c @ $p replacing $replaced with $replacement" }

                    val useSubstitutor = getUseSubstituteMapper(replaced, replacement)
                    patch.replaceCommand(
                        p,
                        listOf(
                            TACCmd.Simple.AssigningCmd.AssignExpCmd(replacement, replaced),
                            useSubstitutor.map(c)
                        )
                    )
                }
            }
        }

        replacements.forEach { p, r ->
            patch.replaceCommand(
                p,
                listOf(r)
            )
        }

        return patch.toCodeNoTypeCheck(code)
    }

}