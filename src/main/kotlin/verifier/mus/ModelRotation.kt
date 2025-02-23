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

package verifier.mus

import datastructures.stdcollections.*
import smt.SmtExpWithLExp
import smtlibutils.algorithms.CollectQualIds
import smtlibutils.cmdprocessor.*
import smtlibutils.data.*
import solver.SolverConfig
import utils.*
import java.io.Closeable

class ModelRotation private constructor(
    baseQuery: SmtFormulaCheckerQuery,
    private val mapSolver: MUSMapSolver,
    private val soft: List<SmtExpWithLExp>,
) : Closeable {
    private val symbolTable = baseQuery.symbolTable
    private lateinit var query: SmtFormulaCheckerQuery
    private val script = SmtScript(symbolTable)
    private lateinit var cmdProcessor: CmdProcessor
    private lateinit var queryProcessor: SmtQueryProcessor

    private val varsToSoft = mutableMapOf<Identifier, MutableSet<Int>>()
    private val softToVars = mutableMapOf<Int, Set<SmtExp.QualIdentifier>>()
    private val varsToHard = mutableMapOf<Identifier, MutableSet<HasSmtExp>>()
    private val hardToVars = mutableMapOf<HasSmtExp, Set<SmtExp.QualIdentifier>>()

    companion object {
        operator suspend fun invoke(
            baseQuery: SmtFormulaCheckerQuery,
            solverConfig: SolverConfig,
            mapSolver: MUSMapSolver,
            soft: List<SmtExpWithLExp>,
            hard: List<HasSmtExp>
        ) = ModelRotation(baseQuery, mapSolver, soft).apply {
            val allTermsOfInterest = mutableSetOf<SmtExp>()

            soft.forEachIndexed { index, exp ->
                val variables = CollectQualIds.collectQualIds(exp)
                allTermsOfInterest.addAll(variables)
                variables.forEach { qId ->
                    varsToSoft.getOrPut(qId.id) { mutableSetOf() }.add(index)
                }
                softToVars[index] = variables
            }

            hard.forEach { exp ->
                val variables = CollectQualIds.collectQualIds(exp)
                allTermsOfInterest.addAll(variables)
                variables.forEach { qId ->
                    varsToHard.getOrPut(qId.id) { mutableSetOf() }.add(exp)
                }
                hardToVars[exp] = variables
            }


            query = SmtFormulaCheckerQuery(
                name = "modelRotationQuery",
                logic = baseQuery.logic,
                symbolTable = symbolTable,
                defineFuns = baseQuery.defineFuns,
                declareDatatypes = baseQuery.declareDatatypes,
                formula = listOf(),
                termsForGetValue = TermsOfInterest(allTermsOfInterest)
            )

            val finalLogic = if (solverConfig.solverInfo.needsLogicALL(query.logic.toSolverConfigLogicFeatures())) {
                Logic.ALL
            } else {
                query.logic
            }

            val solverInstanceInfo = SolverInstanceInfo.fromSolverConfig(
                solverConfig, CmdProcessor.Options.fromQuery(query, incremental = true).copy(
                    logic = finalLogic,
                    produceUnsatCores = false,
                )
            )

            cmdProcessor = ExtraCommandsCmdProcessor.fromSolverInstanceInfo(solverInstanceInfo)
            queryProcessor = SmtQueryProcessor(script, solverInstanceInfo.name, cmdProcessor)
            query.assertFormulaSmtLines(queryProcessor.script).forEach {
                queryProcessor.process(it)
            }
        }
    }

    /**
     * Close the command processor, i.e. the solver process.
     */
    override fun close() {
        cmdProcessor.close()
    }

    private suspend fun getModel(expList: List<SmtExp> = query.termsOfInterest.toList()): Map<SmtExp, SmtExp> =
        queryProcessor.getValue(expList, query.symbolTable)

    /**
     * Critical clauses are those that have to be in the MUS and thus cannot be removed from the current [seed]
     * by the [MUSSubsetSolver.shrink] procedure.
     *
     * Assume that [seed] is UNSAT but the seed without [constraint] c ([seed]-c) is SAT,
     * thus we cannot remove c from the [seed]. Furthermore, there exists a [model] pi for [seed]-c.
     *
     * Now consider any variable v in c and a model pi' such that
     * pi(w) = pi'(w) for every w != v and
     * pi'(v) is such that c and all hard constraints are satisfied.
     *
     * Now some soft constraint is not satisfied by pi' (since the whole [seed] is UNSAT).
     * If there is only one such constraint d then it must be critical: ([seed]-d) is SAT and pi' is its model.
     */
    suspend fun updateCritical(
        constraint: Int,
        criticalConstraints: MutableSet<Int>,
        seed: MutableList<Int>,
        model: Map<SmtExp, SmtExp>,
        blockedBefore: List<Int>? = null
    ) {
        criticalConstraints.add(constraint)

        // If this method was called from shrink, find all constraints satisfying the model and block them in MapSolver.
        // By the assumption, constraints in (seed - c) are satisfied, c is not satisfied by the model.
        val blocked = blockedBefore ?: extendAndBlock(model, seed.filter { it != constraint }, listOf(constraint))

        softToVars[constraint]?.forEach { variable ->
            // skip if a change of variable cannot result in other critical being found
            if (varsToSoft[variable.id]!!.none { it in seed && it !in criticalConstraints }) {
                return@forEach
            }
            // get model where variable v is changed
            // skip if v cannot be changed to satisfy c and all hard constraints
            val modifiedModel = modifyModel(model, constraint, variable) ?: return@forEach
            // check constraints in (seed-c) that are broken by changing v, only those containing v have to be checked
            val notNecessarilySatisfied = satisfiedConstraints(
                modifiedModel,
                varsToSoft[variable.id]!!.intersect(seed).minus(constraint),
            ).second
            if (notNecessarilySatisfied.size == 1 && !criticalConstraints.contains(notNecessarilySatisfied[0])) {
                // Before the recursive call of updateCritical,
                // block the largest SAT set satisfying pi' in the MapSolver.
                // First, compute sets of constraints we know that are/are not satisfied.

                // Satisfied:
                // 1) constraints that were satisfied by the original model that do not contain v
                // 2) constraints in seed except the one that is violated
                val knownSatisfied = blocked.filterTo(mutableSetOf()) {
                    it !in varsToSoft[variable.id]!!
                }.union(seed).minus(notNecessarilySatisfied[0])
                // Not satisfied:
                // 1) constraints that were not satisfied by the original model and do not contain v
                // 2) the one violated constraint in seed
                // Note that the sets knownSatisfied and knownFalsified are disjoint and their union contains
                // all soft constraints except those that contain variable v and are not in the seed.
                val knownFalsified = soft.indices.toSet()
                    .minus(knownSatisfied).minus(varsToSoft[variable.id]!!.minus(seed))

                updateCritical(
                    notNecessarilySatisfied[0],
                    criticalConstraints,
                    seed,
                    modifiedModel,
                    extendAndBlock(modifiedModel, knownSatisfied, knownFalsified)
                )
            }
        }
    }

    /**
     * Given a [model], possibly partial, and list of [constraints],
     * returns which constraints are satisfied and which are not necessarily satisfied by the [model].
     */
    private suspend fun satisfiedConstraints(
        model: Map<SmtExp, SmtExp>,
        constraints: Collection<Int>,
    ): Pair<List<Int>, List<Int>> {
        val mapSmtToInt = constraints.associateBy { soft[it].exp }
        val notNecessarilySatisfied = mutableListOf<Int>()
        val satisfied = mutableListOf<Int>()
        if (constraints.isNotEmpty()) {
            SmtQueryProcessorContext(queryProcessor).use { context ->
                context.push()
                // Insert the partial model to the solver, projected on variables from [constraints]
                CmdProcessor.processAssertCmds(
                    cmdProcessor,
                    getVariablesInSoft(constraints).filter { v -> model[v] != null }.map { v ->
                        script.assertCmd(script.apply(SmtIntpFunctionSymbol.Core.Eq(v.sort!!), v, model[v]!!))
                    }.asSequence(),
                )

                if (queryProcessor.checkSat() !is SatResult.SAT) {
                    error("The asserted model is not valid")
                }

                // Function getValue returns a map where for each constraint (of type SmtExp) we have a boolean value
                // saying if the constraint was satisfied in the last solver check or not. We fill [satisfied] and
                // [notNecessarilySatisfied] based on the values.
                queryProcessor.getValue(constraints.map { soft[it].exp }, symbolTable)
                    .forEachEntry { (constraint, value) ->
                        if (value !is SmtExp.BoolLiteral) {
                            error("Model evaluation result is not a boolean value!")
                        }
                        val c = mapSmtToInt[constraint] ?: return@forEachEntry
                        if (softToVars[c]?.any { model[it] == null} == true) {
                            /**
                             * It could happen that the original [model] was only partial, i.e. not defined for some of
                             * the variables of c. In such case, to be on the safe side, we assume c was not satisfied
                             * by the original model. In particular, it could happen that the partial [model] can be
                             * extended to a model that satisfies [c], however, in other parts of the code, we might
                             * similarly extend the model to satisfy another constraint, say c2, and falsely assume
                             * that the [model] can be extended to satisfy both c and c2 simultaneously. Also, notice
                             * that if c looks e.g. like c = or(v1,v2) and v1 is undefined in [model] but v2 is defined
                             * to be true, [model] in fact satisfies c. We could extend the reasoning to detect such cases,
                             * but we do not do it at this moment.
                             * Another approach we could take here is to actually enforce that [model] is complete at
                             * all locations where we use it, but this might be quite time-consuming.
                             */
                            notNecessarilySatisfied.add(c)
                        } else if(value == SmtExp.BoolLiteral.True) { //the constraint was satisfied in the check
                            satisfied.add(c)
                        } else { //the constraint was not satisfied in the check
                            notNecessarilySatisfied.add(c)
                        }
                    }
            }
        }
        return satisfied to notNecessarilySatisfied
    }

    /**
     * Input:
     * [model] pi - a model for (seed - [constraint])
     * [variable] v - a variable in [constraint] c to be changed
     *
     * Output:
     * model pi' such that
     * - for all w != v: pi(w) = pi'(w)
     * - constraint is satisfied by pi'
     * - all hard constraints are satisfied by pi'
     * if such model exists (if not, return null).
     */
    private suspend fun modifyModel(
        model: Map<SmtExp, SmtExp>,
        constraint: Int,
        variable: SmtExp.QualIdentifier,
    ): Map<SmtExp, SmtExp>? {
        val modifiedModel = model.toMutableMap()

        // Compute new value for v so that c is satisfied
        val modifiedVariable = getModifiedValue(model, constraint, variable) ?: return null

        modifiedModel.putAll(modifiedVariable)

        // Check hard constraints.
        // If there are no hard constraints to check or the check passes, return the model
        if (varsToHard[variable.id] == null || checkHardConstraints(modifiedModel, varsToHard[variable.id]!!)) {
            return modifiedModel
        }
        return null
    }


    /**
     * Input: [model] pi, [constraint] c, [variable] v
     * Output: value of v such that c is satisfied by pi where only v is changed,
     *         null if there is no such value for v
     */
    private suspend fun getModifiedValue(
        model: Map<SmtExp, SmtExp>,
        constraint: Int,
        variable: SmtExp.QualIdentifier,
    ): Map<SmtExp, SmtExp>? {
        SmtQueryProcessorContext(queryProcessor).use { context ->
            context.push()
            // Restrict pi to the variables w in c such that w != v and assert the partial model.
            CmdProcessor.processAssertCmds(
                cmdProcessor,
                // The minus operation demands @Treapable for a potential serialization
                // since we do not need to serialize the result, we can safely suppress the warning from Detekt.
                @Suppress("Treapability")
                softToVars[constraint]!!.minus(variable).filter { v -> model[v] != null }.map { v ->
                    script.assertCmd(script.apply(SmtIntpFunctionSymbol.Core.Eq(v.sort!!), v, model[v]!!))
                }.asSequence()
            )
            // Assert the constraint.
            CmdProcessor.processAssertCmds(
                cmdProcessor,
                sequenceOf(script.assertCmd(soft[constraint].exp)),
            )
            // Get the value of the variable satisfying the constraint if it exists.
            if (queryProcessor.checkSat() !is SatResult.SAT) {
                return null
            }
            return getModel(listOf(variable))
        }
    }

    /**
     * Input: [model] and a collection of [constraints]
     * Output: true iff all [constraints] are satisfied by the [model]
     *
     * The [model] can contain extra variables, they are filtered away before asserting them into the solver.
     * Note: Axioms are not asserted into the solver so some functions may not be evaluated correctly.
     *       In this case, we can get false negative but that will just cause some constraint to be left unmarked as
     *       critical, and it will be checked later during shrink.
     */
    private suspend fun checkHardConstraints(
        model: Map<SmtExp, SmtExp>, constraints: Collection<HasSmtExp>
    ): Boolean {
        SmtQueryProcessorContext(queryProcessor).use { context ->
            context.push()
            // Assert the model
            CmdProcessor.processAssertCmds(
                cmdProcessor,
                getVariablesInHard(constraints).map { v ->
                    script.assertCmd(script.apply(SmtIntpFunctionSymbol.Core.Eq(v.sort!!), v, model[v]!!))
                }.asSequence()
            )

            if (queryProcessor.checkSat() !is SatResult.SAT) {
                error("The asserted model is not valid.")
            }

            // Function getValue returns map where for every constraint we store whether it is satisfied or not.
            // Return true if every constraint is satisfied, i.e., all values in the map are True.
            return queryProcessor.getValue(constraints.map { it.exp }, symbolTable).values.all { lit ->
                lit == SmtExp.BoolLiteral.True
            }
        }
    }

    /**
     * Input:
     * [model] - model satisfying all hard constraints
     * [satConstraints] - soft constraints known to satisfy the [model]
     * [unsatConstraints] - soft constraints known to violate the [model]
     *
     * Calls blockSat for all [soft] constraints satisfying the [model] (not just those previously known).
     */
    private suspend fun extendAndBlock(
        model: Map<SmtExp, SmtExp>, satConstraints: Collection<Int>, unsatConstraints: Collection<Int> = listOf()
    ): List<Int> {
        val constraintsToTry = (soft.indices).filter { it !in satConstraints && it !in unsatConstraints }
        val satisfied = satConstraints.toMutableList()
        if (constraintsToTry.isNotEmpty()) {
            satisfied.addAll(satisfiedConstraints(model, constraintsToTry).first)
        }
        mapSolver.blockSat(satisfied)
        return satisfied
    }


    /**
     * Returns all variables in hard [constraints].
     */
    private fun getVariablesInHard(constraints: Collection<HasSmtExp>): Set<SmtExp.QualIdentifier> {
        val variables = mutableSetOf<SmtExp.QualIdentifier>()
        constraints.forEach { hardToVars[it]?.let { vars -> variables.addAll(vars) } }
        return variables
    }

    /**
     * Returns all variables in soft [constraints].
     */
    private fun getVariablesInSoft(constraints: Collection<Int>): Set<SmtExp.QualIdentifier> {
        val variables = mutableSetOf<SmtExp.QualIdentifier>()
        constraints.forEach { softToVars[it]?.let { vars -> variables.addAll(vars) } }
        return variables
    }

}
