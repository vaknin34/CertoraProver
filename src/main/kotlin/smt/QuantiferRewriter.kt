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

import analysis.storage.StorageAnalysisResult
import com.certora.collect.*
import config.Config
import datastructures.MultiMap
import datastructures.mapAllValues
import datastructures.stdcollections.*
import log.*
import smt.axiomgenerators.fullinstantiation.ArrayGenerator
import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.*
import tac.MetaKey
import utils.*
import vc.data.LExpression
import vc.data.Quantifier
import verifier.PolarityCalculator
import verifier.PolarityCalculator.Polarity
import verifier.SKOLEM_VAR_NAME

private val logger = Logger(LoggerTypes.QUANTIFIERS)

/**
 * Does two things:
 *
 * 1. Removes all exists quantifiers by replacing them with skolem constants. This also works with forall quantifiers
 *    which appear in negative polarity. At the end of this stage there are only forall quantifiers in the formula, and
 *    they are all of positive polarity.
 * 2. Pulls out nested forall quantifiers to be one outer forall on the accumulated variables. This is necessary for our
 *    grounding algorithm.
 *
 * We currently give up on quantified expressions (and on general on grounding) when they are in double polarity.
 * It's a TODO.
 */
class QuantifierRewriter(private val lxf: LExpressionFactory) {

    /** returns null if the polarity is double, otherwise flips the quantifier if polarity is negative */
    private val LExpression.QuantifiedExpr.isActuallyForall: Boolean?
        get() {
            val p = quantifiedVar.first().meta[PolarityCalculator.POLARITY]!!
            if (p == Polarity.BOTH) {
                return null
            }
            return (quantifier == Quantifier.FORALL && p == Polarity.POS) ||
                (quantifier == Quantifier.EXISTS && p == Polarity.NEG)
        }


    /**
     * Returns the skolemized LExpression and true if the expression can be groundable.
     * we can't do stuff if there is an outer forall and within it an exists. An outer exists is not a problem.
     *
     * TODO: handle it using an uninterpreted function that acts as the skolem variable of the inner exists.
     */
    private fun skolemize(original: LExpression): Pair<LExpression, Boolean> {
        var groundable = true

        fun cantGround(msg: String) {
            groundable = false
            if (Config.GroundQuantifiers.get()) {
                // xxx once we have meta for expressions, we could be more specific about the source of
                // grounding failures. Right now, the original expression is not useful for end-users.
                val userMsg = "Can't ground quantifiers, $msg. Either rewrite or turn grounding off."
                logger.warn { "$userMsg Expression is $original" }
                throw CertoraException(
                    CertoraErrorType.GROUNDING_FAIL,
                    userMsg
                )
            }
        }

        fun rec(e: LExpression, withinForall: Boolean): LExpression {

            return when (e) {
                is LExpression.QuantifiedExpr -> {
                    val isActuallyForall = e.isActuallyForall
                    if (isActuallyForall == null) {
                        cantGround("because of double polarity")
                        return e
                    }
                    if (withinForall && !isActuallyForall) {
                        cantGround("because of alternating quantifiers")
                        return e
                    }

                    val newBody = rec(e.body, isActuallyForall)
                    if (isActuallyForall) {
                        if (e.quantifier == Quantifier.FORALL) {
                            e.copyBody(lxf, newBody)
                        } else {
                            lxf { !forall(e.quantifiedVar, !newBody) }
                        }
                    } else {
                        val sub = e.quantifiedVar.associateWith {
                            val name = it.meta[SKOLEM_VAR_NAME] ?: error("Why didn't $it get a skolem var??")
                            lxf.const(name, it.tag, null)
                        }
                        fun sub(exp : LExpression) = sub[exp] ?: exp
                        newBody.transformPost(lxf) { exp ->
                            sub(exp).let { subedExp ->
                                // change the quantified variable to the skolem version in the storage access
                                // meta as well.
                                subedExp.meta[LEXPRESSION_STORAGE_ACCESSES]?.map?.let { originalMap ->
                                    val new = LExpressionStorageAccesses(
                                        originalMap.mapAllValues { _, indices -> indices.map(::sub) }
                                    )
                                    lxf { subedExp.addMeta(LEXPRESSION_STORAGE_ACCESSES, new) }
                                } ?: subedExp
                            }
                        }
                    }
                }

                is LExpression.ApplyExpr ->
                    e.copyArgs(lxf, e.args.map { rec(it, withinForall) })

                else -> e
            }
        }

        return rec(original, false) to groundable
    }


    /**
     * Rewrites [original] with nested quantifiers pulled out to the outer most quantification.
     *
     * TODO: Currently we will exit with an error on cases such as this one:
     *     `forall x. [ forall y. y < 0  /\ forall y. y >= 0 ]`
     *  Because pulling y out will change semantics.
     *  However, this is solvable with simple renaming.
     */
    private fun pullQuantificationOut(original: LExpression): LExpression {

        /** returns the rewritten expression and the quantified variables that were pulled out and not yet reapplied */
        fun rec(e: LExpression, withinQuantifier: Boolean): Pair<LExpression, List<LExpression.Identifier>> =
            when (e) {
                is LExpression.QuantifiedExpr -> {
                    check(e.quantifier == Quantifier.FORALL) {
                        "An exists quantifier should not remain after skolemization $e"
                    }
                    val (newBody, collectedVars) = rec(e.body, true)
                    val newVars = e.quantifiedVar + collectedVars
                    check(newVars.toSet().size == e.quantifiedVar.size + collectedVars.size) {
                        "${Config.GroundQuantifiers.name} Encountered nested quantification with " +
                            "quantified variables of the same name $e"
                    }

                    if (withinQuantifier) {
                        newBody to newVars
                    } else {
                        e.copyQuant(lxf, newVars, newBody) to emptyList()
                    }
                }

                is LExpression.ApplyExpr -> {
                    val results = e.args.map { rec(it, withinQuantifier) }
                    val collectedVars = results.map { it.second }.flatten()
                    check(collectedVars.toSet().size == results.sumOf { it.second.size }) {
                        "${Config.GroundQuantifiers.name} Encountered nested quantification with " +
                            "quantified variables of the same name $e"
                    }
                    e.copyArgs(lxf, results.map { it.first }) to collectedVars

                }

                else -> e to emptyList()
            }

        return rec(original, false).first
    }


    /** Returns the new expression and true if it can be grounded */
    fun rewrite(original: LExpression) =
        if (original.contains { it is LExpression.QuantifiedExpr }) {
            original
                .let(QuantifierSimplifier(lxf)::simplify)
                .let(::skolemize)
                .let { (e, groundable) ->
                    if (groundable) {
                        // we don't bother if we're not going to ground it
                        pullQuantificationOut(e)
                    } else {
                        e
                    } to groundable
                }
        } else {
            original to true
        }


    companion object {

        /**
         * This is an lexpression equivalent of [StorageAnalysisResult.AccessPaths]. It keeps a set of access paths
         * organized by their [StorageAnalysisResult.NonIndexedPath], where for each such non-indexed-path, for each
         * matching access-path, it keeps the list of indices, in lexpression form, related to that path. For example,
         * for storage access `A[x][y]`, it would keep `A[](array access)[](map access)` -> setOf(listOf(x, y)).
         * Of course if more access paths were related to this storage access they would appear in this multimap.
         *
         * Note that the order of indices is important, and is used for matching values to quantified variables in
         * [ArrayGenerator].
         */
        @KSerializable
        @Treapable
        data class LExpressionStorageAccesses(val map: MultiMap<StorageAnalysisResult.NonIndexedPath, List<LExpression>>) :
            AmbiSerializable {
            init {
                check(map.allValues.all { list ->
                    list.all {
                        it.isConst || it is LExpression.Identifier
                    }
                })
            }
        }

        val LEXPRESSION_STORAGE_ACCESSES = MetaKey<LExpressionStorageAccesses>("lexpression.storage.accesses")
    }

}
