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

package analysis.opt

import analysis.TACCommandGraph
import analysis.icfg.ExpressionSimplifier
import datastructures.stdcollections.*
import tac.MetaMap
import vc.data.*

/**
 * credit: shelly
 */
object ConstantPropagator {

    /**
     * With the exception of preserved variables, rewrite all
     * commands and simplify expressions to constants in [code].
     * Assumes no loops (for now).
     */
    fun propagateConstants(
        code: CoreTACProgram,
        preservedNames: Set<String> = setOf(TACKeyword.MEM64.getName())
    ): CoreTACProgram {
        val graph = code.analysisCache.graph

        val preservedVars = preservedVars(graph, code.destructiveOptimizations)

        val mapper = object : DefaultTACCmdMapperWithPointer() {
            val exprSimplifier = ExpressionSimplifier(graph, graph.cache.def, preservedNames, preservedVars)

            override fun mapExpr(expr: TACExpr): TACExpr {
                inv()
                return exprSimplifier.simplify(expr, currentPtr!!, true)
            }

            override fun mapSymbol(t: TACSymbol): TACSymbol {
                inv()
                if (t is TACSymbol.Var && (t in preservedVars || t.namePrefix in preservedNames)) { // don't touch e.g., M0x40
                    return t
                }
                val default = super.mapSymbol(t)
                return if (t is TACSymbol.Var) {
                    exprSimplifier.simplify(t, currentPtr!!, true).getAs<TACExpr.Sym>()?.s ?: default
                } else {
                    default
                }
            }

            // These two overrides are to prevent constants being inlined into the loc tacsymbol.

            override fun mapWordLoad(lhs: TACSymbol.Var, base: TACSymbol.Var, loc: TACSymbol, metaMap: MetaMap) =
                TACCmd.Simple.AssigningCmd.WordLoad(
                    lhs = mapVar(lhs),
                    loc = loc,
                    base = mapVar(base),
                    meta = mapMeta(metaMap)
                )

            override fun mapWordStore(base: TACSymbol.Var, loc: TACSymbol, value: TACSymbol, metaMap: MetaMap) =
                TACCmd.Simple.WordStore(
                    base = mapVar(base),
                    loc = loc,
                    value = mapSymbol(value),
                    meta = mapMeta(metaMap)
                )

        }

        return mapper.mapCommands(code)
    }

    // preserved variables that we don't want to optimize-out during constant propagation
    private fun preservedVars(graph: TACCommandGraph, destructiveOptimizations: Boolean): Set<TACSymbol.Var> {
        val preserve: MutableSet<TACSymbol.Var> = mutableSetOf()

        if (destructiveOptimizations) {
            return preserve
        }

        val cmds = graph.commands.map { it.cmd }

        for (cmd in cmds) {
            cmd.meta[TACMeta.CVL_EXP]?.also {
                preserve.addAll(it.support)
            }

            cmd
                .maybeAnnotation(TACMeta.SNIPPET)
                ?.let { it as? SnippetCmd.CVLSnippetCmd.IfStart }
                ?.also { preserve.add(it.condVar) }
        }

        return preserve
    }
}
