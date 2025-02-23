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

package vc.gen

import analysis.TACCommandGraph
import datastructures.stdcollections.*
import smt.solverscript.LExpressionFactory
import tac.NBId
import vc.data.LExpression
import vc.data.TACExprFactTypeChecked
import vc.data.ToLExpression
import vc.data.TACSymbolTable

/**
 * For a given TACCommandGraph this computes the reachability variables (aka "reach vars") and their defining constraints.
 * Both of which are used by [LeinoWP] to set up the verification condition.
 */
class ReachVars(
    private val g: TACCommandGraph,
    private val lExprFact: LExpressionFactory,
    private val symbolTable: TACSymbolTable,
    txf: TACExprFactTypeChecked = TACExprFactTypeChecked(g.symbolTable),
    private val toLExpAction: (ToLExpression, LExpression) -> Unit
) {

    /* ([NBId] B) -> [ReachVarEquation] of the reachVar of B */
    private val blockToReachVarEq: MutableMap<NBId, ReachVarEquation> =
        ReachVarEquation.getBlockToReachVarEq(g, txf, toLExpAction)

    /* [blockToDependentEqs]: (NBId B) -> the set of all NBIds such that the RHS of their [ReachVarEquation]s
     *  contain occurrences of the reachVar of B. [blockToDependentEqs] can be seen as the dependency graph of ReachVars.
     */
    private val blockToDependentEqs: MutableMap<NBId, MutableSet<NBId>> =
        mutableMapOf<NBId, MutableSet<NBId>>().let { blockToDependentEqs ->
            g.blocks.forEach {
                g.pred(it.id).forEach { pred ->
                    blockToDependentEqs.computeIfAbsent(pred) { mutableSetOf() }.add(it.id)
                }
            }
            blockToDependentEqs
        }

    fun reachVarEqOf(blockId: NBId): ReachVarEquation = blockToReachVarEq[blockId]
        ?: throw IllegalStateException("Expected to find the ReachVarEquation of the block $blockId")

    fun getCurrReachVarEqs(): Set<ReachVarEquation> = blockToReachVarEq.values.toSet()

    fun dependentReachVarEqsOf(blockId: NBId): Set<NBId>? = blockToDependentEqs[blockId]?.toSet()


    fun reachabilityVarEquationOf(blockId: NBId): LExpression =
        ToLExpression(reachVarEqOf(blockId), lExprFact, symbolTable, null, action = toLExpAction)

    fun reachabilityVarDefinitionOf(blockId: NBId): LExpression =
        reachVarEqOf(blockId).rhsDefLExp(lExprFact, symbolTable)


    fun reachabilityVarSubstitutionOf(blockId: NBId): Pair<LExpression.Identifier, LExpression> =
        reachVarEqOf(blockId)
            .let { it.reachIdentLExp(lExprFact, symbolTable) to it.rhsDefLExp(lExprFact, symbolTable) }
}
