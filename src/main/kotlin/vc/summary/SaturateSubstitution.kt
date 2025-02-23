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

package vc.summary

import analysis.worklist.StepResult
import analysis.worklist.WorklistIteration
import com.certora.collect.*
import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.getFreeIdentifiers
import smt.solverscript.functionsymbols.substitute
import utils.containsAny
import vc.data.LExpression
import vc.data.TACExpr
import vc.data.tacexprutil.QuantDefaultTACExprTransformer
import vc.data.tacexprutil.TACExprFreeVarsCollector
import vc.data.tacexprutil.TACExprUtils

/** Version of [SaturateSubstitution] for [LExpression]s. */
class SaturateSubstitutionLExpression(lxf : LExpressionFactory, subs: Map<LExpression.Identifier, LExpression>) :
    SaturateSubstitution<LExpression, LExpression.Identifier>(
        { subs1, exp -> exp.substitute(lxf, subs1) },
        { exp -> exp.getFreeIdentifiers() },
        subs
    )

/** Version of [SaturateSubstitution] for [TACExpr]s. */
class SaturateSubstitutionTACExpr(subs: Map<TACExpr.Sym.Var, TACExpr>) :
    SaturateSubstitution<TACExpr, TACExpr.Sym.Var>(
        { subs1, exp ->
            TACExprUtils.SubstitutorVar(subs1).transform(QuantDefaultTACExprTransformer.QuantVars.Empty, exp)
        },
        { exp -> TACExprFreeVarsCollector.getFreeVars(exp).mapTo(mutableSetOf()) { it.asSym() } },
        subs
    )

/**
 * Iteratively apply [subs] to saturation (i.e. until no variable in the co-domain of [subs] appears in the expression
 * anymore).
 */
abstract class SaturateSubstitution<@Treapable EXP, ID>(
    val substitute: (Map<ID, EXP>, EXP) -> EXP,
    val getFreeVariables: (EXP) -> Set<EXP>,
    val subs: Map<ID, EXP>
) : WorklistIteration<EXP, EXP, EXP>() {

    override fun process(it: EXP): StepResult<EXP, EXP, EXP> {
        val subsRes = substitute(subs, it)
        return if (subs.keys.containsAny(getFreeVariables(subsRes)))
            StepResult.Ok(listOf(subsRes), listOf())
        else
            StepResult.Ok(listOf(), listOf(subsRes))
    }

    override fun reduce(results: List<EXP>): EXP {
        check(results.size == 1)
        return results.first()
    }

}
