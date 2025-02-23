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

package analysis.opt.intervals

import datastructures.MultiMap
import datastructures.stdcollections.*
import tac.NBId
import utils.*
import vc.data.*

/**
 * For every block, considering only commands in the block, returns for every variable, the set of variables that
 * it can be seen as a sole function of. For example:
 * ```
 *   b := c + 3
 *   a := c + 2
 *   d := a * b
 *   e := d + d + 3
 *   f := e + e
 * ```
 * Here, `f` can be seen single-variable function of `e`, of `d`, and of `c`, but not `a` or `b`.
 * We call these the "deciding" variables for `f`.
 */
class OneVarExpressions(code: CoreTACProgram) {
    val g = code.analysisCache.graph

    interface Res {
        /** Constants are ignored */
        object Const : Res

        /**
         * Can be seen as a single-variable function of any of the variables is [s]. If [s] is empty, it is different
         * than [Const], because it means this is in fact a non-const function but of at least two variables.
         */
        data class Vars(val s: Set<TACSymbol.Var>) : Res
    }


    private fun handleExpr(e: TACExpr, decidingVars: MultiMap<TACSymbol.Var, TACSymbol.Var>): Res {
        if (when (e) {
                is TACExpr.Sym.Const -> return Res.Const
                is TACExpr.Sym.Var -> return Res.Vars(decidingVars[e.s].orEmpty() + e.s)
                is TACExpr.BinBoolOp,
                is TACExpr.BinOp,
                is TACExpr.BinRel,
                is TACExpr.TernaryExp,
                is TACExpr.UnaryExp,
                is TACExpr.Vec -> true

                is TACExpr.Apply ->
                    when ((e.f as? TACExpr.TACFunctionSym.BuiltIn)?.bif) {
                        is TACBuiltInFunction.SafeMathPromotion,
                        is TACBuiltInFunction.SafeMathNarrow,
                        is TACBuiltInFunction.NoAddOverflowCheck,
                        is TACBuiltInFunction.TwosComplement.Wrap,
                        is TACBuiltInFunction.TwosComplement.Unwrap,
                        is TACBuiltInFunction.NoMulOverflowCheck,
                        is TACBuiltInFunction.NoSAddOverAndUnderflowCheck,
                        is TACBuiltInFunction.NoSSubOverAndUnderflowCheck,
                        is TACBuiltInFunction.NoSMulOverAndUnderflowCheck -> true

                        else -> false
                    }

                else -> false
            }
        ) {
            val opValues = e.getOperands()
                .map { handleExpr(it, decidingVars) }
                .filterIsInstance<Res.Vars>()
                .map { it.s }
            return if (opValues.isEmpty()) {
                Res.Const
            } else {
                Res.Vars(opValues.foldFirst { i, j -> i intersect j })
            }
        }
        return Res.Vars(emptySet())
    }


    /**
     * Traversing the cmds forwards, calculates for each variable which variables decide it.
     */
    private fun oneVarExpressions(b: NBId): MultiMap<TACSymbol.Var, TACSymbol.Var> {
        /** We just ignore these for simplicity */
        val assignedAfterUsed = run {
            val used = mutableSetOf<TACSymbol.Var>()
            g.lcmdSequence(b).mapNotNull { (_, cmd) ->
                used += cmd.getFreeVarsOfRhs()
                cmd.getLhs().takeIf {
                    it in used
                }
            }
        }.toSet()

        return buildMap {
            g.lcmdSequence(b)
                .map { it.cmd }
                .filterIsInstance<TACCmd.Simple.AssigningCmd.AssignExpCmd>()
                .forEach { cmd ->
                    if (cmd.freeVars().any { it in assignedAfterUsed }) {
                        return@forEach
                    }
                    val lhs = cmd.lhs
                    (handleExpr(cmd.rhs, this@buildMap) as? Res.Vars)?.let {
                        this[lhs] = it.s
                    }
                }
        }
    }


    fun go(): Map<NBId, MultiMap<TACSymbol.Var, TACSymbol.Var>> {
        val info = g.blocks.map { it.id }.associateWith { oneVarExpressions(it) }
        return info
    }

}
