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

package smt.axiomgenerators.fullinstantiation

import smt.axiomgenerators.AxiomContainer
import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.AxiomatizedFunctionSymbol
import smt.solverscript.functionsymbols.FunctionSymbol
import smt.solverscript.functionsymbols.NrOfParameters
import vc.data.LExpression

object BijectionAxiomHelper {
    /**
     * Adds "inverse function constraints" for the given set of application expressions.
     */
    fun addPointwiseInverseFunctions(
        axiomContainer: AxiomContainer,
        indexToInvFs: (Int) -> FunctionSymbol,
        applyExps: Collection<LExpression.ApplyExpr>,
    ) {
        applyExps.forEach { app ->
            val arity = app.args.size
            repeat(arity) { i ->
                axiomContainer.addAxioms(
                    "pointwise inverse at index $i" to
                        {
                            applyExp(
                                indexToInvFs(i),
                                app
                            ) eq app.args[i]
                        }
                )
            }
        }
    }

    /**
     * This can be used for instance for disambiguating hash functions with different arities; e.g. to add axioms like
     *  arity_disambig(hash_2(x, y)) = 2
     *  arity_disambig(hash_2(u, v)) = 2
     *  arity_disambig(hash_7(x, y)) = 7
     *  etc.
     * This is basically an instance of the inverse function trick to ensure that the terms that are mapped to
     * something different by `arity_disambig` cannot be the same (due to `arity_disambig` being a function).
     *
     * Everything that gets some "disambiguationId" here is forced to be different from everything that gets a different
     * "disambiguationId" (2 and 7 in the above example are examples of "disambiguationIds").
     *
     * @param appToDisambiguationId allows to assign a "disambiguationId" per each individual hash application
     * @param expsToDisambiguate the function applications in the program that should be disambiguated(/"grouped")
     * @param disAmbigFunction the function symbol to use for the disambiguating function
     */
    fun addDisambiguation(
        axiomContainer: AxiomContainer,
        appToDisambiguationId: (LExpression) -> LExpression,
        expsToDisambiguate: Collection<LExpression>,
        disAmbigFunction: AxiomatizedFunctionSymbol,
    ) {
        expsToDisambiguate.forEach { app ->
            axiomContainer.addAxioms(
                "disambiguate arities through quasi-inverse function" to
                        { applyExp(disAmbigFunction, app) eq appToDisambiguationId(app) }

            )
        }
    }

    fun axiomatizeFunctionsAsInverses(
        axiomContainer: AxiomContainer,
        lxf: LExpressionFactory,
        fs1: AxiomatizedFunctionSymbol,
        argumentTuples1: Collection<List<LExpression>>,
        fs2: AxiomatizedFunctionSymbol,
        argumentTuples2: Collection<List<LExpression>>,
    ) {
        fun makeAxiom(
            argumentTuples: Collection<List<LExpression>>,
            base: AxiomatizedFunctionSymbol,
            inverse: AxiomatizedFunctionSymbol,
        ) {
            require((inverse.signature.nrOfParameters as? NrOfParameters.Fixed)?.n == 1)
            { "can't axiomatize a function (here: $inverse) as inverse of another when it doesn't have exactly one parameter" }
            require(inverse.signature.getParamSort(0) == base.signature.resultSort) {
                "signatures of function symbols don't allow axiomatizing them as inverses (function symbols: " +
                        "\"$base\" , \"$inverse\" ; signatures: \"${base.signature}\", \"${inverse.signature}\")"
            }
            require(argumentTuples.all { it.size == 1 })
            { "arguments don't match function -- function signature allows one argument, but got a different number" }
            argumentTuples.forEach { args ->
                axiomContainer.addAxiom(
                    lxf { applyExp(inverse, applyExp(base, args)) eq args.first() },
                    description = "$inverse is the inverse of  $base"
                )
            }
        }
        makeAxiom(argumentTuples1, fs1, fs2)
        makeAxiom(argumentTuples2, fs2, fs1)
    }
}
