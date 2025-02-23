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

package analysis

import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol
import vc.data.tacexprutil.QuantDefaultTACExprTransformer


object DefiningEquationAnalysis {

    private class InvalidRHSException : Exception()

    private class Worker(
        private val g: TACCommandGraph,
        private val target: CmdPointer,
        private val expressionFilter: (TACExpr) -> Boolean
    ) {

        private val block = g.elab(target.block)

        fun process(start: CmdPointer, sym: TACSymbol.Var): TACExpr? {
            var pos = start.pos
            var track = sym
            while(pos >= target.pos) {
                val lc = block.commands[pos]
                if (lc.cmd !is TACCmd.Simple.AssigningCmd || lc.cmd.lhs != track) {
                    pos--
                    continue
                }
                if(lc.cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
                    return null
                }
                val exp = lc.cmd.rhs
                if(exp is TACExpr.Sym) {
                    if(exp is TACExpr.Sym.Var) {
                        track = exp.s
                        pos--
                        continue
                    }
                    check(exp.s is TACSymbol.Const)
                    return exp
                }
                return object : QuantDefaultTACExprTransformer() {
                    override fun transform(acc: QuantVars, exp: TACExpr): TACExpr {
                        if(!expressionFilter(exp)) {
                            throw InvalidRHSException()
                        }
                        if(exp !is TACExpr.Sym) {
                            return super.transform(acc, exp)
                        }
                        if(exp !is TACExpr.Sym.Var) {
                            return exp
                        }
                        return if(pos == target.pos) {
                            exp
                        } else {
                            this@Worker.process(block.commands[pos-1].ptr, exp.s) ?: throw InvalidRHSException()
                        }
                    }
                }.transformOuter(exp)
            }
            return TACExpr.Sym(track)
        }

    }

    /**
     * Find the defining equation for the variable [v] in graph [g] at the point of [where],
     * where the equation is given in terms of the values of variables right before executing [target].
     * In other words, we can express the value of [v] at [where] and the equation will hold right before [target].
     */
    fun getDefiningEquation(g: TACCommandGraph, v: TACSymbol.Var, where: CmdPointer, target: CmdPointer, expressionFilter: (TACExpr) -> Boolean = {
        true
    }) : TACExpr? {
        if(where.block != target.block || where.pos < target.pos) {
            return null
        }
        if(where.pos == target.pos) {
            return v.asSym()
        }
        return try {
            Worker(g, target, expressionFilter).process(where, v)
        } catch(_: InvalidRHSException) {
            null
        }
    }
}
