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

package vc.data.state

import datastructures.Bijection
import log.Logger
import log.LoggerTypes
import utils.mapNotNullToSet
import utils.mapToSet
import vc.data.TACSymbol
import java.util.*

private val logger = Logger(LoggerTypes.TAC_INTERPRETER)

/**
 * The actual state structure used by the Interpreter.
 * @param canonicalVarAssignment mapping each canonical variable to its value in the state.
 * @param tacLockedVars list of TAC variables that should always be initialized and should never change
 * @param tacToCanonicalTable translation table from TAC variable to its canonical representation
 *
 * kotlin serialization is used in order to dump as a json file.
 * Invariant that should be kept in the state:
 * 1. No Uninitialized value. Variables that don't have a value and are not in tagsWithDefaultInitialization should not
 *    appear in th state.
 * 2. variables with tag in tagsWithDefaultInitialization should appear in the state from the point of their assign
 * 3. reset should also preserve 1 and 2.
 *    (havoc) and be initialized to their initial value.
 */
open class ConcreteTACState(
    private val canonicalVarAssignment: Map<TACSymbol.Var, TACValue>,
    val tacLockedVars: Set<TACSymbol.Var>,
    private val tacToCanonicalTable: Bijection<TACSymbol.Var, TACSymbol.Var>,
) : TACState {

    @Suppress("Unused", "UnusedPrivateMember")
    private val debugTable: Map<TACSymbol.Var, TACValue>? =
        if (debugMode) {
            computeDebugTable(canonicalVarAssignment, tacToCanonicalTable)
        } else {
            null
        }

    private fun computeDebugTable(
        canonicalVarAssignment: Map<TACSymbol.Var, TACValue>,
        tacToCanonicalTable: Bijection<TACSymbol.Var, TACSymbol.Var>
    ): Map<TACSymbol.Var, TACValue> {
        return canonicalVarAssignment.mapKeys { (k, _) ->
            tacToCanonicalTable.reverseGet(k) ?: error("could not find value in tacToCanonicalTable for key \"$k\"")
        }
    }


    companion object {

        /**
         * Validate that [state] complies with the following guidelines -
         * 1. All locked variables are initialized.
         * 2. All variables in [canonicalVarAssignment] are in their canonical form according to the translation table
         */
        private fun validateState(state: ConcreteTACState): Boolean {
            return state.tacLockedVars.all { state.isInitialized(it) }
                    && state.canonicalVarAssignment.all { state.tacToCanonicalTable.containsValue(it.key) }
        }

        private fun validateReachVarsStateSwitch(
            from: ConcreteTACState,
            to: ConcreteTACState,
            allReachVars: Collection<TACSymbol.Var>
        ): Boolean{
            return allReachVars.all {
                to.isInitialized(it) && // we always initialize all reach vars
                        (!from.isInitialized(it) ||
                                // we may not go from true to false
                                (from.get(it) != TACValue.PrimitiveValue.Bool(true) ||
                                    to.get(it) != TACValue.PrimitiveValue.Bool(false))
                                )
            }
        }

        /**
         * Validate that both [from] and [to] are valid according to the guidelines above. Also, validate that the
         * transition is valid according to the following guidelines -
         * 1. The translation tables are the same in both states.
         * 2. [to]'s locked vars contains all of [from]'s locked vars.
         */
        fun validateStateSwitch(from: ConcreteTACState, to: ConcreteTACState, allReachVars: Collection<TACSymbol.Var>): Boolean {
            return validateState(from) && validateState(to)
                    && from.tacToCanonicalTable == to.tacToCanonicalTable   // canonicalTransTable should never change
                    && to.tacLockedVars.containsAll(from.tacLockedVars)     // notToReset should be append-only
                    && validateReachVarsStateSwitch(from, to, allReachVars)

        }

        /**
         * Returns an empty state
         */
        fun createEmptyConcreteTACState(): ConcreteTACState {
            return ConcreteTACState(emptyMap(), emptySet(), Bijection())
        }

        const val debugMode = false // must be `false` in master
    }

    /**
     * Checks if a TAC variable holds an initialized value
     * True iff this partial state has a meaningful assignment for `canonicalVar`.
     * If this is `false` for every entry in [canonicalVarAssignment], then this state is an empty state.

     * @param [v] - variable before canonization]
     */
    @Suppress("Unused")
    fun hasNonInitialValue(v: TACSymbol.Var): Boolean =
        canonicalHasNonInitialValue(translateToCanonicalVar(v))


    /**
     * True if this state has a meaningful value for `v`.
     */
    fun isInitialized(v: TACSymbol.Var): Boolean =
        canonicalAndInitialized(translateToCanonicalVar(v))

    private fun canonicalAndInitialized(canonicalVar: TACSymbol.Var): Boolean {
        val assignedValue = canonicalVarAssignment[canonicalVar] ?: return false
        return assignedValue != TACValue.Uninitialized
    }

    /**
     * Translate [v] to its canonical form according to the translation table
     */
    private fun translateToCanonicalVar(v: TACSymbol.Var): TACSymbol.Var {
        return tacToCanonicalTable[v]
            ?: error("found unknown TAC var. var=$v")
    }

    /**
     * Add [v] to the set of locked variables (always initialized and never modified)
     * @param[v] - tac variable
     */
    fun lockVar(v: TACSymbol.Var): ConcreteTACState {
        return ConcreteTACState(canonicalVarAssignment, this.tacLockedVars.plus(v), tacToCanonicalTable)
    }

    /**
     * Add vars in varsToLock to the set of locked variables (always initialized and never modified)
     */
    fun lockVars(varsToLock: Set<TACSymbol.Var>): ConcreteTACState{
        return ConcreteTACState(canonicalVarAssignment, this.tacLockedVars.plus(varsToLock), tacToCanonicalTable)
    }

    /**
     * unlock and update locked variable @param[v]. Locak it again.
     */
    fun updateLockedVar(v: TACSymbol.Var, newValue: TACValue): ConcreteTACState{
        val newState = unlockAndUninitializeVar(v)
        return newState.storeVar(v, newValue).lockVar(v)
    }

    /**
     * unlock v and remove its canonical var from state. In order to update it afterwards.
     */
    private fun unlockAndUninitializeVar(v: TACSymbol.Var): ConcreteTACState{
        val canonV = translateToCanonicalVar(v)
        check(canonV in canonicalVarAssignment){"Trying to unlock uninitialized variable $v"}
        return ConcreteTACState(canonicalVarAssignment.minus(canonV), tacLockedVars.minus(v), tacToCanonicalTable)
    }

    /**
     * Lock all initialized variables
     */
    fun lockAllInitializedVars(): ConcreteTACState {
        val initTacVars = tacToCanonicalTable.filterKeys { isInitialized(it) }.keys
        return ConcreteTACState(canonicalVarAssignment, initTacVars, tacToCanonicalTable)
    }

    /**
     * @return - the value of v in the state.
     * Returns TACValue.Uninitialized for uninitialized variables (lhs of assign havoc).
     * The only assignment get should return if absent is uninitialized.
     */
    override operator fun get(v: TACSymbol.Var): TACValue {
        val canonV = translateToCanonicalVar(v)
        return canonicalVarAssignment[canonV] ?: TACValue.Uninitialized
    }

    /**
     * Uninitialized values should not be stored.
     * for value == uninitialized:
     * If v has a default value, the default value is stored.
     * Otherwise the state does not change.
     * Store initialized [value]  as the value of [v]
     */
    override fun storeVar(v: TACSymbol.Var, value: TACValue): ConcreteTACState {
        val initializedValue = value
        if (value == TACValue.Uninitialized) {
            return this
        }
        var canonV = v
        if (tacToCanonicalTable.containsKey(v)) { // v is a non-canonical var (i.e. TAC var)
            canonV = translateToCanonicalVar(v)
            check(!tacLockedVars.contains(v) || !canonicalVarAssignment.containsKey(canonV) ||
                    canonicalVarAssignment[canonV] == value)
            { "trying to update a protected var. var=$v, currValue=${canonicalVarAssignment[canonV]}" }
        }
        check(tacToCanonicalTable.containsValue(canonV)) { " found a var that is neither canonical or a TAC var. var=$canonV" }
        return ConcreteTACState(canonicalVarAssignment.plus(Pair(canonV, initializedValue)), tacLockedVars,
            tacToCanonicalTable)
    }

    /**
     * Batch store of variables and their values
     */
    fun storeVars(vs: Map<TACSymbol.Var, TACValue>): ConcreteTACState {
        var newState = this
        vs.forEach { newState = newState.storeVar(it.key, it.value) }
        return newState
    }

    /**
     * Batch store of values as stored in [from]
     */
    @Suppress("Unused")
    fun storeVars(from: ConcreteTACState): ConcreteTACState {
        return storeVars(from.canonicalVarAssignment)
    }

    /**
     * If [toReset] is not null, remove all unlocked variables in [toReset] from the state.
     * If [toReset] is null, remove all unlocked variables from the state.
     *
     * IMPORTANT: this is used for different goals:
     * 1. Resetting variables that affect the condition before sending to the solver. In this case toReset is
     *    either lhs of AssignHavoc or variables that depend on lhs of assignhavoc.
     * 2. Resetting the unused variables for which the solver gave an assignment.
     */
    fun resetVars(toReset: Set<TACSymbol.Var>? = null): ConcreteTACState {
        val toResetCanonical = toReset?.mapNotNullToSet { tacToCanonicalTable[it] }
        val tacLockedVarsCanonical = tacLockedVars.mapToSet { tacToCanonicalTable[it] }
        val resetState =  ConcreteTACState(
            canonicalVarAssignment.filterKeys { sym -> sym in tacLockedVarsCanonical ||
                    toResetCanonical?.contains(sym) == false },
            tacLockedVars,
            tacToCanonicalTable,
        )
        return resetState
    }

    /**
     * Remove the reach vars from the state assignments.
     */
    fun removeReachVarsAssignments(reachVars: Collection<TACSymbol.Var>): ConcreteTACState {
        var newState = this
        reachVars.forEach {
            newState = newState.unlockAndUninitializeVar(it)
        }
        return newState
    }

    /**
     * True iff this partial state has a meaningful assignment for [canonicalVar].
     *
     * If this is `false` for every entry in [canonicalVarAssignment], then this state is an empty state.
     *
     * NB: we might clean this up some time by never storing these values in [canonicalVarAssignment] in the first
     *   place.
     */
    private fun canonicalHasNonInitialValue(canonicalVar: TACSymbol.Var): Boolean {
        val assignedValue = canonicalVarAssignment[canonicalVar] ?: return false
        return assignedValue.isNonInitialValue()
    }

    /**
     * Return a mapping keyed with TAC variables (non-canonical vars as declared in the TAC program).
     */
    fun getTACVarAssignment(): Map<TACSymbol.Var, TACValue> {
        val tacVars = mutableMapOf<TACSymbol.Var, TACValue>()
        tacToCanonicalTable.forEach { tacVar, canonicalVar ->
            if (canonicalHasNonInitialValue(canonicalVar)) {
                tacVars[tacVar] = canonicalVarAssignment[canonicalVar]!!
            }
        }
        return tacVars
    }

    fun debugPrint(title: String) {
        logger.debug { title }
        for (v in canonicalVarAssignment.entries) {
            logger.debug { v.toString() }
        }
    }

    fun initializedState(): ConcreteTACState {
        return ConcreteTACState(
            canonicalVarAssignment.filter { it.value != TACValue.Uninitialized },
            tacLockedVars,
            tacToCanonicalTable,
        )
    }

    fun getMapFromVarNameToValue(): Map<String, TACValue> {
        return canonicalVarAssignment.mapKeys {
            it.key.toString()
        }
    }

    override fun equals(other: Any?): Boolean {
        return other is ConcreteTACState && this.canonicalVarAssignment == other.canonicalVarAssignment
    }

    override fun hashCode(): Int {
        return Objects.hash(this.canonicalVarAssignment, this.tacLockedVars, this.tacToCanonicalTable)
    }

    /**
     * A state is empty if it either has no vars or all its vars are empty WordMap/ByteMap
     */
    fun isEmpty(reachVars: Collection<TACSymbol.Var>): Boolean {
        val canonicalReachVars = tacToCanonicalTable.filter {it.key in reachVars }.values
        val initializedVars = canonicalVarAssignment.filter { it.value != TACValue.Uninitialized &&
                it.key !in canonicalReachVars}
        return initializedVars.isEmpty()
    }

    fun hasValuation(v: TACSymbol.Var): Boolean {
        return if (v !in tacToCanonicalTable) {
            false
        } else {
            val canonv = tacToCanonicalTable[v]
            canonv in canonicalVarAssignment && canonicalVarAssignment[canonv] != TACValue.Uninitialized
        }
    }

    /**
     * Returns the number of uninitialized variables in the CFG.
     * Used to compare the number of uninitialized variables before/after a heuristic.
     */
    fun uninitializedVars(definedVars: Set<TACSymbol.Var>): Set<TACSymbol.Var> =
        definedVars.filter { !canonicalAndInitialized(it) }.toSet()

}
