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

import config.Config
import datastructures.stdcollections.*
import kotlinx.coroutines.flow.toList
import log.Logger
import log.LoggerTypes
import smt.SmtExpWithLExp
import smtlibutils.algorithms.CollectQualIds
import smtlibutils.cmdprocessor.*
import smtlibutils.data.*
import solver.SolverConfig
import utils.*
import vc.data.lexpression.META_AUTO_GENERATED_ASSERT
import vc.data.lexpression.META_TOPLVL_CMD
import java.io.Closeable
import kotlin.time.Duration.Companion.seconds
import kotlin.time.TimeMark
import kotlin.time.Duration as kDuration

typealias Subset = List<Int>

private val logger = Logger(LoggerTypes.MUS_ENUMERATION)

/**
 * Computes minimal UNSAT subsets (MUS).
 * https://sun.iwu.edu/~mliffito/publications/constraints_liffiton_marco.pdf
 * https://github.com/liffiton/marco/
 *
 * S: set of soft constraints corresponding to TAC assignments, assume and assert commands
 * H: set of hard constraints corresponding to the rest (e.g. path conditions, labels, annotations, axioms)
 *
 * We introduce one smt constant for each soft constraint, we call them [identifiers].
 *
 * (We actually fix a formula of all hard constraints that contains for each soft constraint s_i the implication
 * a_i => s_i, where a_i is its corresponding identifier.
 * Each subset of soft constraints is then given by the boolean values of all [identifiers],
 * i.e., a_i = true iff s_i is in the subset.)
 *
 *
 * <Think power set lattice of soft constraints>
 * We keep track of unexplored sets in the powerset using the [MUSMapSolver] class
 *
 *  MapSolver
 *   data:
 *     // models of this formula are the unexplored sets
 *     F: boolean formula over [identifiers] in CNF
 *
 *   blockUnsat(mus: Set<identifiers>)
 *     update F such that every superset of mus is marked as explored
 *
 *   blockSat(mss: Set<identifiers>)
 *     update F such that every subset of mss is marked as explored
 *
 *   getMaxUnexplored()
 *     call solver on F to get a new unexplored subset and then maximizes it
 *
 *
 *  main:
 *
 *  input: S, H (where S+H are UNSAT)
 *  output: muss (list of MUSes)
 *
 *   while (mapSolver.hasUnexplored)
 *     unExp = mapSolver.getMaxUnexplored()
 *
 *     res = smt.check(unExp, H)
 *
 *     when (res.satResult)
 *         SAT ->
 *            // unExp must be a MSS, due to its maximality
 *            mapSolver.blockSat(res)
 *       UNSAT ->
 *            // unExp may or may not me _minimal_ unsatisfiable set
 *            mus = shrink(res.unsatCore)
 *            muss.add(mus)
 *            mapSolver.blockUnsat(mus)
 *
 *
 *  shrink:
 *   input: unsat set of soft constraints
 *   output: minimal unsat set of soft constraints (subset of the input)
 *   <incrementally removes elements, until none can be removed, uses solver's unsat cores to speed up the process>
 */
class MUSSubsetSolver private constructor(
    baseQuery: SmtFormulaCheckerQuery,
    val userDefinedHard: MutableSet<SmtExpWithLExp>
) : Closeable {
    lateinit var query: SmtFormulaCheckerQuery
    val soft = mutableListOf<SmtExpWithLExp>()
    val symbolTable = baseQuery.symbolTable
    val script: SmtScript = SmtScript(symbolTable)
    private val identifiers = mutableListOf<SmtExp>()
    private val identifierMap = mutableMapOf<SmtExp, Int>()
    private val muses = mutableListOf<Subset>()
    private lateinit var cmdProcessor: CmdProcessor
    private lateinit var queryProcessor: SmtQueryProcessor
    private lateinit var mapSolver: MUSMapSolver

    private val initialUnsatCore = mutableListOf<Int>()

    private lateinit var modelRotation: ModelRotation
    private val unsatCoreLimit: Int = Config.NumOfUnsatCores.get()
    private var startTimeOfEnumeration: TimeMark? = null
    private val enumerationTimeout: kDuration = Config.UnsatCoresEnumerationTimeout

    companion object {
        operator suspend fun invoke(
            baseQuery: SmtFormulaCheckerQuery,
            solverConfig: SolverConfig,
            userDefinedHard: MutableSet<SmtExpWithLExp> = mutableSetOf(),
        ) = MUSSubsetSolver(baseQuery, userDefinedHard).apply {
            val allTermsOfInterest = mutableSetOf<SmtExp>()
            val hard = mutableListOf<HasSmtExp>()
            val unsatCore = try {
                (baseQuery.coreHelper?.coreAsSmtExps ?: baseQuery.formula()).toSet()
            } catch (e: UninitializedPropertyAccessException) {
                logger.warn { "The unsatCoreHelper is not null but the UNSAT core was not processed. " + e.message }
                baseQuery.formula().toSet()
            }

            userDefinedHard.filter { it !in baseQuery.formula() }.let { undefinedConstraints ->
                if (undefinedConstraints.isNotEmpty()) {
                    logger.warn {
                        "MUSSubsetSolver got ${undefinedConstraints.size} userDefinedHard constraints " +
                            "that are not in the baseQuery. Ignoring those."
                    }
                    userDefinedHard.removeAll(undefinedConstraints.toSet())
                }
            }

            val formula = mutableListOf<HasSmtExp>()
            baseQuery.formula().forEach { exp ->
                allTermsOfInterest.addAll(CollectQualIds.collectQualIds(exp))
                if (exp !in userDefinedHard && exp.isSoftConstraint()) {
                    exp as SmtExpWithLExp //telling the compiler the type of exp; enforced by the call of exp.isSoftConstraint()
                    // The non-user asserts appear in the UNSAT core, therefore, the function calls part of the analysis
                    // does not work properly. We replace them by trivial asserts.
                    if (!Config.UnsatCoresForAllAsserts.get() && META_AUTO_GENERATED_ASSERT in exp.lexp.meta
                        && exp.exp is SmtExp.Apply.Binary
                    ) {
                        val trivialAssert = script { (exp.exp as SmtExp.Apply.Binary).args.first() eq boolLit(true) }
                        formula.add(trivialAssert)
                        hard.add(trivialAssert)
                        return@forEach
                    }
                    val identifier = script.id("activator${identifiers.size}", Sort.BoolSort)
                    allTermsOfInterest.add(identifier)
                    symbolTable.registerDeclFun(identifier.id, listOf(), Sort.BoolSort)
                    identifiers.add(identifier)
                    identifierMap[identifier] = identifiers.size - 1
                    formula.add(script { identifier implies exp.exp })
                    soft.add(exp)
                    if (exp.exp in unsatCore) {
                        initialUnsatCore.add(identifiers.size - 1)
                    }
                } else {
                    formula.add(exp)
                    hard.add(exp)
                }
            }

            query = SmtFormulaCheckerQuery(
                name = baseQuery.info.name,
                logic = baseQuery.logic,
                symbolTable = symbolTable,
                defineFuns = baseQuery.defineFuns,
                declareDatatypes = baseQuery.declareDatatypes,
                formula = formula,
                termsForGetValue = TermsOfInterest(allTermsOfInterest),
                getUnsatCore = false
            )

            val finalLogic = if (solverConfig.solverInfo.needsLogicALL(query.logic.toSolverConfigLogicFeatures())) {
                Logic.ALL
            } else {
                query.logic
            }
            val solverInstanceInfo = SolverInstanceInfo.fromSolverConfig(
                solverConfig,
                CmdProcessor.Options.fromQuery(query, incremental = true).copy(
                    logic = finalLogic,
                    produceUnsatCores = true,
                )
            )

            cmdProcessor = ExtraCommandsCmdProcessor.fromSolverInstanceInfo(solverInstanceInfo)
            queryProcessor = SmtQueryProcessor(script, solverInstanceInfo.name, cmdProcessor)
            query.assertFormulaSmtLines(queryProcessor.script).forEach {
                queryProcessor.process(it)
            }

            // The map solver queries are solved easily, therefore, the 5 seconds should be sufficient.
            mapSolver = MUSMapSolver(soft.size, timeout = 5.seconds)
            modelRotation = ModelRotation(baseQuery, solverConfig, mapSolver, soft, hard)
        }
    }

    /**
     * Obtain the model. Should only be called immediately after a SAT result.
     */
    private suspend fun getModel(): Map<SmtExp, SmtExp> =
        queryProcessor.getValue(query.termsOfInterest.toList(), query.symbolTable)

    /**
     * Close the command processor, i.e. the solver process.
     */
    override fun close() {
        cmdProcessor.close()
    }

    /**
     * Checks satisfiability of the subset of soft constraints.
     * If UNSAT, returns an UNSAT core consisting of soft constraints (all hard are always assumed),
     * if SAT returns a model.
     */
    private suspend fun check(seed: Subset): CheckResult {
        SmtQueryProcessorContext(queryProcessor).use { context ->
            context.push()
            val assumptions = seed.map {
                check(it >= 0 && it < identifiers.size) { "The given index $it does not correspond to an identifier" }
                identifiers[it]
            }

            val localUcHelper = CoreHelper(assumptions, SmtScript(query.symbolTable))
            CmdProcessor.processAssertCmds(
                cmdProcessor, assumptions.map { script.assertCmd(it.exp) }.asSequence(), localUcHelper
            )
            val satResult: SatResult = queryProcessor.checkSat()

            val model = if (satResult is SatResult.SAT) {
                getModel()
            } else {
                null
            }

            val core = if (satResult is SatResult.UNSAT) {
                localUcHelper.parseCore(solverOutput = cmdProcessor.getUnsatCore().toList())
                val intCore = mutableListOf<Int>()
                localUcHelper.coreAsSmtExps.forEach { assumption ->
                    intCore.add(identifierMap[assumption]!!)
                }
                intCore
            } else {
                null
            }

            return CheckResult(satResult, core, model)
        }
    }

    /**
     * Single MUS extraction subroutine.
     *
     * Input is a set of constraints that is UNSAT. We minimize this set by removing constraints one by one
     * while keeping the set UNSAT.
     * If a constraint can be removed, we use an UNSAT core from the solver to remove potentially more constraints.
     * If a constraint cannot be removed, we apply model rotation to prove that other constraints cannot be removed
     * as well (this is implemented in [ModelRotation.updateCritical]). We call these criticalConstraints.
     */
    private suspend fun shrink(seed: MutableList<Int> = (0 until identifiers.size).toMutableList()): Subset {
        var core = seed.toMutableList()
        val criticalConstraints = mutableSetOf<Int>()
        for (index in seed) {
            // If the constraint is critical, it cannot be removed, therefore we will not attempt it.
            // If the constraint is not present in the seed because we already removed it before, move on.
            if (index in criticalConstraints || !core.remove(index)) {
                continue
            }
            // An invariant of the for cycle is that the core is an UNSAT unexplored set.
            // Every superset of UNSAT explored set is also explored (see the mapSolver.blockUnsat function).
            // Therefore, if core - {index} is explored, it has to be SAT (since its superset core is unexplored).
            if (mapSolver.isExploredSat(core, index)) {
                core.add(index)
                criticalConstraints.add(index)
                continue
            }
            val checkResult = check(core)
            when (checkResult.result) {
                // We cannot remove the constraint. Try model rotation to prove that other constraints cannot
                // be removed and put them in [criticalConstraints].
                SatResult.SAT -> {
                    core.add(index)
                    modelRotation.updateCritical(index, criticalConstraints, core, checkResult.model!!)
                }

                SatResult.UNSAT -> {
                    if (checkResult.unsatCore != null) {
                        core = checkResult.unsatCore
                    }
                }

                else -> {
                    core.add(index)
                    logger.warn { "Could not solve query during shrink procedure." }
                }
            }
            if (startTimeOfEnumeration!!.elapsedNow() > enumerationTimeout) {
                logger.warn { "Exceeded the timelimit ($enumerationTimeout) for Unsat Cores Enumeration (when shrinking)." }
                break
            }
        }
        return core
    }

    /**
     * Method for computing soft constraints of all MUSes. Each MUS is stored as list of indices.
     *
     * We repeatedly asks [MUSMapSolver] for unexplored sets of soft constraints and check their satisfiability.
     * If SAT, the set is MSS, and we mark all its subsets as explored in the [MUSMapSolver].
     * If UNSAT, we minimize the set thus obtaining MUS. We mark its supersets as explored in the [MUSMapSolver].
     */
    private suspend fun computeMUSes() {
        startTimeOfEnumeration = getCurrentTime()
        // Start with the unsat core from the original query.
        val firstMUS = shrink(initialUnsatCore)
        muses.add(firstMUS)
        mapSolver.blockUnsat(firstMUS)

        while (muses.size < unsatCoreLimit) {
            val seed = mapSolver.getMaximalUnexplored() ?: break
            val checkResult = check(seed)
            when (checkResult.result) {
                SatResult.SAT -> mapSolver.blockSat(seed)
                SatResult.UNSAT -> {
                    val mus = shrink(checkResult.unsatCore as MutableList<Int>)
                    muses.add(mus)
                    mapSolver.blockUnsat(mus)
                }

                else -> {
                    logger.warn { "Maximal unexplored set could not be solved." }
                    break
                }
            }
            if (startTimeOfEnumeration!!.elapsedNow() > enumerationTimeout) {
                logger.warn { "Exceeded the timelimit ($enumerationTimeout) for Unsat Cores Enumeration." }
                break
            }
        }
    }

    fun getInitialUnsatCore() = initialUnsatCore.map { soft[it] } + userDefinedHard

    /**
     * Returns the list of MUSes. Each MUS is represented as a list of SMT expressions
     * with the corresponding LExpression.
     */
    suspend fun getMUSes(): List<List<SmtExpWithLExp>> {
        computeMUSes()
        return muses.map { mus ->
            /**
             * We have to add the userDefinedHard constraints to the returned unsat cores - they belong to the unsat cores,
             * even though it might mean that the unsat cores are not minimal. Read the comment in [UnsatCoreAnalysis].
             */
            mus.map { soft[it] } + userDefinedHard
        }
    }

    /**
     * Returns the list of constraints contained in every computed MUS.
     */
    fun getIntersection(): List<SmtExpWithLExp> {
        return mapSolver.getConstraintFrequency().mapIndexedNotNull { index, frequency ->
            if (frequency == muses.size) {
                soft[index]
            } else {
                null
            }
        }
    }
}


data class CheckResult(val result: SatResult, val unsatCore: MutableList<Int>?, val model: Map<SmtExp, SmtExp>?)


fun HasSmtExp.isSoftConstraint() = this is SmtExpWithLExp && META_TOPLVL_CMD in this.lexp.meta
