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

package smt

import datastructures.stdcollections.*
import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.*
import tac.MetaMap
import utils.`impossible!`
import vc.data.LExpression
import vc.data.Quantifier

/**
 * Simplifier for quantified formulas.
 *
 * Currently provides two simplifications, [eliminateUnused], and [destructiveEqualityResolution].
 * [simplify] bundles the two.
 *
 * All the simplifications return equivalent formulas (so no approximation going on).
 *
 * Glossary: Using `juncts` for when it could be either con- or disjuncts.
 *
 * future work:
 *  - some normalizations beforehand might make this more effective
 *  - the special case solution for `implies` isn't so pretty ..
 */
class QuantifierSimplifier(val lxf: LExpressionFactory) {

    /**
     * Runs all the simplifications implemented here on all the quantified subexpressions of [exp].
     */
    fun simplify(exp: LExpression): LExpression =
        exp.transformPost(lxf) {
            it
                .let(::eliminateUnused)
                .let(::eliminateForallImplications)
                .let(::flattenQuantifiedJunctions)
                .let(::destructiveEqualityResolution)
        }

    /**
     * Applies a simplification to all the quantified subexpressions of [exp].
     * The simplification removes all quantifier bindings that are never used in the quantified formula's body.
     * `[forall|exists] x. Phi` ~~> `Phi` where `x` is not a free variable in `Phi`
     */
    private fun eliminateUnused(exp: LExpression): LExpression =
        when (exp) {
            is LExpression.QuantifiedExpr -> {
                val bodyVars = exp.body.getFreeIdentifiers()
                // taking care to keep the original metas of the quantified variables.
                val usedQVars = exp.quantifiedVar.filter { it in bodyVars }
                if (usedQVars.isEmpty()) {
                    exp.body
                } else if (usedQVars == exp.quantifiedVar) {
                    exp // nothing changed, no need to make a copy
                } else {
                    exp.copyQuant(lxf, newVars = usedQVars.toList())
                }
            }
            else -> exp
        }

    /**
     * flattens nested junctions -- another normalization in preparation for [destructiveEqualityResolution]
     *
     * note that for a real normal form, this would have to be integrated with [eliminateForallImplications] since
     * they might interact, but for now that case (i.e. a discjunction inside an implication) seems sufficiently
     * irrelevant. */
    private fun flattenQuantifiedJunctions(exp: LExpression): LExpression {
        fun collectJuncts(e : LExpression, fs : FunctionSymbol) : List<LExpression> =
            if (e is LExpression.ApplyExpr && e.f == fs) {
                e.args.flatMap { collectJuncts(it, fs) }
            } else {
                listOf(e)
            }

        return when (exp) {
            is LExpression.QuantifiedExpr ->  {
                val flattenedBody = when {
                    exp.body.isApplyOf<TheoryFunctionSymbol.Vec.LAnd>() ->
                        lxf.and(collectJuncts(exp.body, TheoryFunctionSymbol.Vec.LAnd), exp.meta, simplify = true)
                    exp.body.isApplyOf<TheoryFunctionSymbol.Vec.LOr>() ->
                        lxf.or(collectJuncts(exp.body, TheoryFunctionSymbol.Vec.LOr), exp.meta, simplify = true)
                    else ->
                        exp.body
                }
                exp.copyQuant(lxf, newBody = flattenedBody)
            }

            else -> exp
        }
    }

    /**
     * Transformation in preparation for [destructiveEqualityResolution]
     * Eliminates implications that occur directly under a `forall` quantifier.
     *
     * `forall x. A -> B` ~~> `forall x. (not A) \/ B`
     */
    private fun eliminateForallImplications(exp: LExpression): LExpression =
        when (exp) {
            is LExpression.QuantifiedExpr -> when {
                exp.quantifier == Quantifier.FORALL && exp.body.isApplyOf<TheoryFunctionSymbol.Binary.LImplies>() ->
                    exp.copyQuant(lxf, newBody = lxf { !exp.body.lhs or exp.body.rhs })
                else -> exp
            }
            else -> exp
        }


    /** Intermediate result for [destructiveEqualityResolution] when eliminating a chain of same-polarity
     * quantifications */
    private data class DerRes(
        val quantifier: Quantifier,
        val couldNotBeEliminated: List<LExpression.Identifier>,
        val juncts: List<LExpression>,
        val junctionMeta: MetaMap, // let no meta be lost
    ) {
        /**
         * When all variables have been processed, this builds the final result as a (potentially) quantified expression.
         * [originalQExpMeta] is the meta of the original quantified expression, to be merged with the meta from the elimination
         * result */
        fun buildFinal(lxf: LExpressionFactory, originalQExpMeta: MetaMap): LExpression {
            val junction = when (quantifier) {
                Quantifier.FORALL -> lxf.or(juncts, junctionMeta + originalQExpMeta, simplify = true)
                Quantifier.EXISTS -> lxf.and(juncts, junctionMeta + originalQExpMeta, simplify = true)
            }
            return lxf.buildQuantifiedExpr(quantifier, couldNotBeEliminated, junction)
        }
    }



    /**
     * Applies a simplification on all the quantified subexpressions of [exp].
     * The simplification is sometimes called "destructive equality resolution" or similar.
     * `exists x. x == t /\ Phi(x)` ~~> `Phi(t)` where x does not appear in t
     *   and the dual
     * `forall x. x != t \/ Phi(x)` ~~> `Phi(t)` where x does not appear in t
     *   as well as the implication-case (basically subsumed by the disjunction)
     * `forall x. x == t -> Phi(x)` ~~> `Phi(t)` where x does not appear in t
     *
     * Concrete examples:
     * `exists x. x == 13 /\ y > x` would be simplified to `y > 13`
     * `forall x. x == 13 -> y > x` would be simplified to `y > 13`
     */
    private fun destructiveEqualityResolution(exp: LExpression): LExpression =
        when (exp) {
            is LExpression.QuantifiedExpr ->
                when {
                    (exp.quantifier == Quantifier.EXISTS &&
                        exp.body.isApplyOf<TheoryFunctionSymbol.Vec.LAnd>() &&
                        exp.body.args.size > 1 // just making sure..
                        ) ||
                        (exp.quantifier == Quantifier.FORALL &&
                            exp.body.isApplyOf<TheoryFunctionSymbol.Vec.LOr>() &&
                            exp.body.args.size > 1 // just making sure..
                            ) -> {

                        exp.quantifiedVar.foldRight(
                                DerRes(exp.quantifier, listOf(), exp.body.args, exp.body.meta)
                            ) { qVar, intermediateRes ->
                                val qVarDef = extractQVarDefIfPossible(exp.quantifier, qVar, intermediateRes.juncts)
                                if (qVarDef != null) {
                                    // pattern matching successful -- eliminating [qVar]
                                    val newJuncts = lxf {
                                        qVarDef.otherJuncts
                                            .map { it.substituteQuantified(lxf, mapOf(qVar to qVarDef.qVarDefinition)) }
                                    }
                                    intermediateRes.copy(juncts = newJuncts)
                                } else {
                                    // pattern matching unsuccessful -- add [qVar] to [couldNotBeEliminated]
                                    intermediateRes.copy(couldNotBeEliminated = intermediateRes.couldNotBeEliminated + qVar)
                                }
                            }.buildFinal(lxf, exp.meta)
                    }

                    exp.quantifier == Quantifier.FORALL &&
                        exp.body.isApplyOf<TheoryFunctionSymbol.Binary.LImplies>() -> {
                        error("implications under forall quantifiers should have been eliminated in " +
                            "favour of disjunctions before running this (DER) transformation (got: $exp)")
                    }

                    else -> exp
                }
            else -> exp
        }


    /** Extract the DER-pattern into a [QVarDefinition], returns null if the pattern is not matched. */
    private fun extractQVarDefIfPossible(
        quantifier: Quantifier,
        qVar: LExpression.Identifier,
        juncts: List<LExpression>
    ): QVarDefinition? {
        /** checking whether [eq] is of the form  `qVar == t` where `qVar` is not a free var in `t` */
        fun isEquationDefinitionQVar(eq: LExpression): Boolean =
            if (!eq.isApplyOf<TheoryFunctionSymbol.Binary.Eq>()) {
                false
            } else {
                val (qVarOccurrences, other) = eq.args.partition { it == qVar }
                qVarOccurrences.size == 1 &&
                    other.size == 1 &&
                    (qVar !in other.single().getFreeIdentifiers())
            }

        fun juncHasEqDef(junct: LExpression): Boolean =
            when (quantifier) {
                Quantifier.FORALL ->
                    junct.isApplyOf<TheoryFunctionSymbol.Unary.LNot>() && isEquationDefinitionQVar(junct.arg)
                Quantifier.EXISTS ->
                    isEquationDefinitionQVar(junct)
            }

        val (eqsWithQVar, others) = juncts.partition(::juncHasEqDef)

        return if (eqsWithQVar.isNotEmpty()) {
            QVarDefinition(
                qVar,
                eqsWithQVar.first() as LExpression.ApplyExpr,
                others + eqsWithQVar.drop(1),
            )
        } else {
            null
        }
    }

    /**
     * Helper datastructure for the DER-pattern.
     *
     * @param qVar the quantified variable that is to be eliminated`
     * @param definingJunct the [con|dis]junct that has the definition of the quantified variable
     * @param otherJuncts the [con|dis]juncts in the quantifier body except for [definingJunct]
     */
    private class QVarDefinition(
        qVar: LExpression.Identifier,
        definingJunct: LExpression.ApplyExpr,
        val otherJuncts: List<LExpression>,
    ) {
        private fun defFromEquality(qVar:LExpression.Identifier, eq: LExpression.ApplyExpr): LExpression =
            if (eq.lhs == qVar) {
                eq.rhs
            } else {
                check(eq.rhs == qVar) { "equation \"$eq\" is supposed to have variable \"$qVar\" either on its " +
                    "lhs or rhs, but doesn't." }
                eq.lhs
            }

        /** The side of [definingJunct] that is not [qVar]. */
        val qVarDefinition: LExpression =
            when {
                definingJunct.isApplyOf<TheoryFunctionSymbol.Unary.LNot>() -> {
                    val arg = definingJunct.arg
                    check(arg.isApplyOf<TheoryFunctionSymbol.Binary.Eq>()) {
                        "must have a negated equality here, got: $definingJunct"
                    }
                    defFromEquality(qVar, arg)
                }
                definingJunct.isApplyOf<TheoryFunctionSymbol.Binary.Eq>() ->
                    defFromEquality(qVar, definingJunct)
                else -> `impossible!`
            }

    }

}
