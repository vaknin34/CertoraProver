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

package solver

import datastructures.stdcollections.*
import smt.solverscript.functionsymbols.TheoryFunctionSymbol
import smt.solverscript.functionsymbols.asConst
import smt.solverscript.functionsymbols.isNumericLiteral
import tac.NBId
import tac.Tag
import utils.KSerializable
import vc.data.*
import vc.data.state.TACValue
import vc.gen.LeinoWP
import java.math.BigInteger

// TODO probably could replace functionality by SatResult.SAT or something adjacent, nb reachable bad blocks may need some thought, calldata stuff, too
// not sure about this --> all that SMT stuff lives in SMTLibUtils and can't use things like NBId, LExpression etc
@KSerializable
data class SMTCounterexampleModel(
    override val tacAssignments: Map<TACSymbol.Var, TACValue>,
    var reachableBadNBIds: Set<NBId> = emptySet(),
    private val missingReachVarDefinitions: Map<NBId, LExpression> = emptyMap(),
    private val consolidatedEdgeBlocks: Map<NBId, Map<NBId, Set<NBId>>> = emptyMap(),
    override val havocedVariables: Set<TACSymbol.Var> = emptySet()
): CounterexampleModel() {

    override val reachableNBIds: Set<NBId>
        get() = tacAssignments
            .filterKeys { TACMeta.LEINO_REACH_VAR in it.meta }
            .filterValues { it == TACValue.True }
            .mapTo(mutableSetOf()) { it.key.meta[TACMeta.LEINO_REACH_VAR]!! } // this never throws a NPE because of the filter two lines above

    override val unreachableNBIds: Set<NBId>
        get() = tacAssignments
            .filterKeys { TACMeta.LEINO_REACH_VAR in it.meta }
            .filterValues { it == TACValue.False }
            .mapTo(mutableSetOf()) { it.key.meta[TACMeta.LEINO_REACH_VAR]!! } // this never throws a NPE because of the filter two lines above

    val badNBIds: Set<NBId>
        get() = tacAssignments
            .filterKeys { TACMeta.LEINO_OK_VAR in it.meta }
            .filterValues { it == TACValue.False }
            .mapTo(mutableSetOf()) { it.key.meta[TACMeta.LEINO_OK_VAR]!! } // this never throws a NPE because of the filter two lines above

    fun getAssignmentsToMissingOKVars(): Map<TACSymbol.Var, TACValue> {
        val missingOkVarsAssgnToFalse: MutableMap<TACSymbol.Var, TACValue> = mutableMapOf()
        consolidatedEdgeBlocks.forEachEntry { (block, succToCebs) ->
            if (tacAssignments[LeinoWP.genOkIdentOf(block)] == TACValue.False) {
                succToCebs.forEachEntry { (succ, cebs) ->
                    if (tacAssignments[LeinoWP.genOkIdentOf(succ)] == TACValue.False) {
                        cebs.map { LeinoWP.genOkIdentOf(it) }
                            .associateWithTo(missingOkVarsAssgnToFalse) {
                                TACValue.False
                            }
                    }
                }
            }
        }
        return missingOkVarsAssgnToFalse
    }

    fun getAssignmentOfMissingReachVar(block: NBId): Boolean? = missingReachVarDefinitions[block]?.let {
        evalReachVarDef(it)
    }

    private fun evalReachVarDef(reachVarDef: LExpression): Boolean =
        when (reachVarDef) {
            is LExpression.Identifier -> {
                tacAssignments[TACSymbol.Var(reachVarDef.id, Tag.Bool)].let { value ->
                    if (value is TACValue.PrimitiveValue.Bool) {
                        value.value
                    } else {
                        throw IllegalStateException(
                            "Expected a Boolean assignment value for the identifier $reachVarDef, but got \"$value\""
                        )
                    }
                }
            }
            is LExpression.ApplyExpr -> {
                when (reachVarDef.f) {
                    is TheoryFunctionSymbol.Unary.LNot -> {
                        check(reachVarDef.args.size == 1)
                        !evalReachVarDef(reachVarDef.args.first())
                    }
                    is TheoryFunctionSymbol.Binary.Eq -> {
                        check(reachVarDef.args.size == 2)
                        val arg0 = reachVarDef.args[0]
                        val arg1 = reachVarDef.args[1]
                        if (arg0.isNumericLiteral && arg0.asConst == BigInteger.ZERO) {
                            !evalReachVarDef(arg1)
                        } else if (arg1.isNumericLiteral && arg1.asConst == BigInteger.ZERO) {
                            !evalReachVarDef(arg0)
                        } else {
                            throw UnsupportedOperationException("Cannot eval $reachVarDef")
                        }
                    }
                    is TheoryFunctionSymbol.Vec.LAnd -> {
                        reachVarDef.args.forEach { currArg ->
                            val evalOfCurrArg: Boolean = evalReachVarDef(currArg)
                            if (!evalOfCurrArg) {
                                return@evalReachVarDef false
                            }
                        }
                        true
                    }
                    else -> {
                        throw UnsupportedOperationException("Cannot eval $reachVarDef")
                    }
                }
            }
            else -> throw UnsupportedOperationException("Cannot eval $reachVarDef")
        }

    fun setReachableBadBlocks(reachableBadblocks: Set<NBId>) {
        reachableBadNBIds = reachableBadblocks
    }

    fun getReachableBadBlocks(): Set<NBId> = reachableBadNBIds

    override fun getAssignmentOf(v: TACSymbol.Var) = this.tacAssignments[v]
    override fun cvlAssignments(fullyProcessedTAC: CoreTACProgram): Map<String, TACValue> {
        val allVariables = mutableSetOf<TACSymbol.Var>()
        // get all the variables in the TAC Program
        fullyProcessedTAC.ltacStream().forEach { lc ->
            val cmd = lc.cmd
            cmd.getLhs()?.let { lhs -> allVariables.add(lhs) }
            cmd.getRhs().filterIsInstance<TACSymbol.Var>().forEach { rhsVar -> allVariables.add(rhsVar) }
        }

        // map from CVL Name to TAC Name(s)
        val extractedSymbolAllocations = mutableMapOf<String, MutableSet<TACSymbol.Var>>()
        // get all relevant tac names for each cvl name
        allVariables.forEach { v ->
            v.meta.find(TACMeta.CVL_DISPLAY_NAME)?.let { cvlName ->
                // namePrefix or smtRep?
                extractedSymbolAllocations.getOrPut(cvlName) { mutableSetOf() }.add(v)
            }
        }


        // map from tac name to it's originating cvl name
        val tacVarToCVLName = mutableMapOf<TACSymbol.Var, String>()
        extractedSymbolAllocations.entries.forEach { (cvlName, tacVars) ->
            val firstModel = tacVars.firstOrNull()?.let { tacVar -> tacAssignments[tacVar] }
            // it is possible for multiple instances of a given identifier in a cvl program (for example, x could be
            // a parameter to a rule, and a parameter to a cvl function), so there is no way to be guaranteed that
            // a cvl identifier corresponds to a unique value (though it often does) and when it does, then we can
            // ask what the value (in the *global* counterexample) was given to that identifier. The below condition
            // does not necessarily correspond to this condition "cvl id corresponds to unique tac value" (I'm not
            // sure how we would check this since the value may pass through multiple variables), however, for our
            // purposes, it is sufficient to ask "does this cvl id correspond to a unique counterexample/model
            // value?" which is what this condition checks. Only when this condition is met do we add this to the
            // cvl variable model
            if (tacVars.all { tacVar -> tacAssignments[tacVar] == firstModel }) {
                tacVars.forEach { tacVar -> tacVarToCVLName[tacVar] = cvlName }
            }
        }

        // copy variable model to cvl versions of variables
        return tacAssignments.mapNotNull { (varName, model) ->
            // if there is no tac->cvl name mapping, the entry should not be in the counterexample
            tacVarToCVLName[varName]?.let { cvlName ->
                // because of the condition above, while we may be reassigning to newAssignments[cvlName],
                // we will be reassigning the same model
                cvlName to model
            }
        }.toMap()
    }

    companion object {
        val Empty = SMTCounterexampleModel(mapOf())
    }
}

