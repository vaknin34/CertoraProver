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

import algorithms.topologicalOrder
import datastructures.stdcollections.*
import log.Logger
import log.LoggerTypes
import smt.solverscript.LExpressionFactory
import smt.solverscript.functionsymbols.*
import vc.data.LExpression

private val logger = Logger(LoggerTypes.SMT_VARIABLE_INLINER)

/**
 * A simple utility to inline a set of variables within [LExpression]. The set of variables to be inlined is given as
 * [variables]. Then, the list of assertions is shown to it via [identifyElimination] which identifies the assertions suitable for
 * eliminating one of the variables from [variables], [inlineEliminations] will then flatten the eliminations by
 * inlining every elimination in all others, and then [inline] will replace these variables from the given
 * [LExpression].
 *
 * [inlineEliminations] first establishes a topological ordering of the eliminations so that a single linear sweep is
 * sufficient for a complete flattening. This assumes that there are no recursive substitutions, which the caller is
 * responsible for.
 */
class VariableInliner(
    val lxf: LExpressionFactory,
    val variables: Set<LExpression>,
) {
    /**
     * The current eliminations. No right hand side should contain any of the left hand sides, which [addElimination]
     * tries to make sure.
     */
    val eliminations: MutableMap<LExpression,LExpression> = mutableMapOf()

    /**
     * Adds the elimination [lhs] to [rhs] to [eliminations]. Does some basic checks to detect cyclic eliminations.
     */
    private fun addElimination(lhs: LExpression, rhs: LExpression) {
        // If any of the checks within this function fails, it probably means that there is a loop in the eliminations
        // and we need to be more careful in handling these.
        check(lhs !in rhs.getFreeIdentifiers())
        check(!eliminations.containsKey(lhs))
        eliminations[lhs] = rhs
        logger.debug { "Eliminating ${lhs} -> ${rhs}" }
    }

    /**
     * Check [exp] whether it can be used as an elimination for one of [variables]. If so it returns `true` and the
     * assertion [exp] can be dropped from the overall formula.
     */
    fun identifyElimination(exp: LExpression): Boolean {
        if (exp.isApplyOf<TheoryFunctionSymbol.Binary.Eq>()) {
            if (exp.lhs in variables && !eliminations.containsKey(exp.lhs)) {
                addElimination(exp.lhs, exp.rhs)
                return true
            } else if (exp.rhs in variables && !eliminations.containsKey(exp.rhs)) {
                addElimination(exp.rhs, exp.lhs)
                return true
            }
        } else if (exp.isApplyOf<NonSMTInterpretedFunctionSymbol.Binary.AssignEq>()) {
            if (exp.lhs in variables && !eliminations.containsKey(exp.lhs)) {
                addElimination(exp.lhs, exp.rhs)
                return true
            }
        }
        return false
    }

    /**
     * Flatten all eliminations by inlining them into each other.
     */
    fun inlineEliminations() {
        val start = System.currentTimeMillis()
        val curMap = mutableMapOf<LExpression,LExpression>()
        eliminations.map {
            // (eliminated variable, substitute expression, variables from substitute expression)
            Triple(it.key, it.value, it.value.getFreeIdentifiers())
        }.let { trips ->
            // order so that a variable is eliminated before any of those in the substitute expression
            // -> a.first in b.third => b before a
            topologicalOrder(trips, { a -> trips.filter { b -> a.first in b.third }}).asReversed()
        }.forEach { (l,r,_) ->
            val inlined = r.substitute(lxf, curMap)
            curMap[l] = inlined
            logger.debug { "Inlined ${l} -> ${r} -> ${inlined}" }
        }
        eliminations.clear()
        eliminations.putAll(curMap)
        logger.info { "Inlined eliminations in ${(System.currentTimeMillis() - start)}ms" }
    }

    /**
     * Performs all substitutions on [exp] that were previously collected via [identifyElimination].
     */
    fun inline(exp: LExpression): LExpression = exp.substitute(lxf, eliminations)
}
