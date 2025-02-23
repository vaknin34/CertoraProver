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

import datastructures.Bijection
import vc.data.tacexprutil.TACExprFolder
import vc.summary.TACTransFormula

class CollectDefinitionsTACExpr private constructor(val definedVars: Set<TACExpr.Sym.Var>) : TACExprFolder<Unit>() {
    private val result = mutableMapOf<TACExpr.Sym.Var, TACExpr>()

    override fun expr(acc: Unit, v: TACExpr) = when (v) {
        is TACExpr.BinRel.Eq -> {
            if (v.o1 in definedVars) result[v.o1 as TACExpr.Sym.Var] = v.o2
            if (v.o2 in definedVars) result[v.o2 as TACExpr.Sym.Var] = v.o1
            Unit
        }
        is TACExpr.BinBoolOp.LAnd -> {
            v.ls.forEach { super.expr(Unit, it) }
            Unit
        }
        else -> Unit // do nothing
    }

    companion object {
        fun computeDefinitions(
            tf: TACTransFormula,
            definedVars: Set<TACExpr.Sym.Var>
        ): Map<TACExpr.Sym.Var, TACTransFormula> {
            val cd = CollectDefinitionsTACExpr(definedVars)
            cd.expr(Unit, tf.exp)
            /**
             * for each definition build a special transformula (which not describes a transition... hm...) whose exp
             * is the value of the definition, and whose inVars map the definitions vars to TaCSummaryVars
             * this is analogue to [CollectDefinitionsLExp]
             */
            return cd.result.mapValues { (_, exp) ->
                val varsInExp = TACTransFormula.getVariables(exp)
                TACTransFormula(
                    exp,
                    Bijection.fromMap(tf.inVars.filter { (_, symVar) -> symVar in varsInExp }),
                    Bijection(),
                    setOf(),
                    tf.auxVars.filter { it in varsInExp }.toSet()
                )
            }
        }
    }

    override fun const(acc: Unit, v: TACSymbol.Const) = Unit

    override fun variable(acc: Unit, v: TACSymbol.Var) = Unit
}