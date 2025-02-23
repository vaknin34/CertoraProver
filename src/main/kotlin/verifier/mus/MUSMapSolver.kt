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
import smtlibutils.cmdprocessor.*
import smtlibutils.data.*
import solver.Z3SolverInfo
import java.io.Closeable
import kotlin.time.Duration

/**
 * This class is a part of the minimal unsatisfiable subset (MUS) computation implemented in [MUSSubsetSolver].
 * The MUS computation effectively explores the powerset of a (conjunctive) set of constraints.
 * This class is responsible for tracking which constraints sets have not already been explored by the MUS computation.
 *
 * We use integers to map the set of constraints (of size [n]) from the MUS computation to the [identifiers].
 */
class MUSMapSolver private constructor(val n: Int) : Closeable {
    val symbolTable = SmtSymbolTable()
    private lateinit var cmdProcessor: CmdProcessor
    private lateinit var queryProcessor: SmtQueryProcessor
    lateinit var query: SmtFormulaCheckerQuery
    val script = FactorySmtScript.withSymbolTable(symbolTable)
    private val identifiers = (1..n).map {
        script.qualIdentifier(Identifier.Simple("a$it"), null, Sort.BoolSort)
    }
    private val muses = mutableListOf<Set<Int>>()
    private val satSubsets = mutableListOf<Set<Int>>()

    // for each constraint, we store a set of MUSes (indexes in muses list) containing this constraint
    private val musesTouchingConstraint = List(n) { mutableSetOf<Int>() }
    private val satSubsetsNotTouchingConstraint = List(n) { mutableSetOf<Int>() }

    companion object {
        operator suspend fun invoke(n: Int, timeout: Duration) = MUSMapSolver(n).apply {
            /**
            * register/declare the activation variables in the symbol table
            */
            identifiers.forEach {
                symbolTable.registerDeclFun(FactorySmtScript.simpleIdentifier(it.toString()), listOf(), Sort.BoolSort)
            }

            /**
            * create "true" smt formula over the symbol table
            */
            query = SmtFormulaCheckerQuery(
                name = "mapSolver",
                logic = Logic.QF_CORE,
                symbolTable = symbolTable,
                defineFuns = listOf(),
                declareDatatypes = listOf(),
                formula = listOf(script.boolLit(true)), //initially Map is set to true
                termsForGetValue = TermsOfInterest(identifiers.toSet())
            )

            val solverInstanceInfo = SolverInstanceInfo.fromSolverConfig(
                Z3SolverInfo.plainConfig(timelimit = timeout, incrementalMode = true),
                CmdProcessor.Options.fromQuery(query, incremental = true).copy(
                    logic = Logic.ALL,
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

    /**
     * Returns arbitrary unexplored set of constraints (any unexplored set is a model of the formula we keep),
     * null if there is no unexplored set to return.
     */
    private suspend fun getUnexplored(): Subset? {
        return if (queryProcessor.checkSat() is SatResult.SAT) {
            val model = queryProcessor.getValue(query.termsOfInterest.toList(), query.symbolTable)
            return identifiers.mapIndexedNotNull { index, identifier ->
                if (model[identifier] == script.boolLit(true)) index else null
            }
        } else {
            null
        }
    }

    /**
     * Finds a maximal unexplored set of constraints.
     *
     * First, we get an arbitrary unexplored set by asking for a model of a formula we keep in a [query].
     * Then we maximize the set by adding constraints one by one while keeping the set unexplored.
     */
    suspend fun getMaximalUnexplored(): Subset? {
        val seed = getUnexplored() as MutableList<Int>?
        if (seed != null) {
            val compl = complement(seed)
            compl.forEach {
                seed.add(it)
                if (!isNotExploredUnsat(seed.toSet(), it)) {
                    seed.remove(it)
                }
            }
        }
        return seed
    }

    /**
     * Returns (set) complement of a given seed.
     */
    private fun complement(seed: Subset): Subset {
        return (0 until n).filter { it !in seed }
    }

    /**
     * Marks every subset of the [seed] as explored.
     *
     * The added constraint (block) is satisfied iff at least one element of the complement is in the subset.
     */
    suspend fun blockSat(seed: Subset) {
        val block = script { or(complement(seed).map { identifiers[it] }) }
        CmdProcessor.processAssertCmds(
            cmdProcessor,
            sequenceOf(script.assertCmd(block.exp)),
        )
        complement(seed).forEach { constraint ->
            satSubsetsNotTouchingConstraint[constraint].add(satSubsets.size)
        }
        satSubsets.add(seed.toSet())
    }

    /**
     * Marks every superset of the [seed] as explored.
     *
     * The added constraint (block) is satisfied iff at least one element of the seed is not in the subset.
     */
    suspend fun blockUnsat(seed: Subset) {
        val block = script { or(seed.map { not(identifiers[it]) }) }
        CmdProcessor.processAssertCmds(
            cmdProcessor,
            sequenceOf(script.assertCmd(block.exp)),
        )
        seed.forEach { constraint ->
            musesTouchingConstraint[constraint].add(muses.size)
        }
        muses.add(seed.toSet())
    }

    /**
     * Input: [seed] containing [addedConstraint] such that ([seed] - [addedConstraint]) is unexplored
     * Output: true iff the [seed] is unexplored
     *
     * Set is explored iff it is a subset of some already found SAT subset or a superset of some already found MUS.
     * Since [seed] without the [addedConstraint] is an unexplored set, we cannot have a subset of SAT subset.
     * Therefore, we just check that adding this constraint does not make the set a superset of some MUS.
     */
    private fun isNotExploredUnsat(seed: Set<Int>, addedConstraint: Int): Boolean {
        return musesTouchingConstraint[addedConstraint].none { mus ->
            seed.containsAll(muses[mus])
        }
    }

    /**
     * Input: ([seed] + [removedConstraint]) is unexplored UNSAT set
     * Output: true iff [seed] is explored
     *
     * Since [seed] + [removedConstraint] is unexplored, it cannot be superset of any explored MUS.
     * For this reason, the only way [seed] may be explored is if it is a subset of some explored SAT set.
     * In this case we also know that [seed] is SAT.
     */
    fun isExploredSat(seed: Collection<Int>, removedConstraint: Int): Boolean {
        return satSubsetsNotTouchingConstraint[removedConstraint].any { satSubset ->
            satSubsets[satSubset].containsAll(seed)
        }
    }


    /**
     * Returns a list such that on index i is a number of muses that contain constraint i.
     */
    fun getConstraintFrequency(): List<Int> {
        return musesTouchingConstraint.map { it.size }
    }

}
