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

package verifier.cegar

import datastructures.stdcollections.*
import log.*
import parallel.coroutines.RaceFinish
import smtlibutils.algorithms.CollectFunctionSymbols
import smtlibutils.algorithms.CollectQualIds
import smtlibutils.cmdprocessor.*
import smtlibutils.data.FactorySmtScript
import smtlibutils.data.Logic
import smtlibutils.data.SmtExp
import smtlibutils.data.SmtIntpFunctionSymbol
import solver.SolverConfig
import utils.*
import java.io.Closeable
import java.util.*
import java.util.concurrent.atomic.AtomicInteger

/**
 * A utility to use a bunch of [Closeable] objects in a block and safely close all of them at the end and properly
 * dealing with all exceptions (that might be thrown by the block itself or any of the objects during close).
 *
 * If no exception is thrown, returns whatever the block returns.
 * If the block throws, re-throws that "main" exception after closing all objects and adds all exceptions that were
 * thrown during closing to that "main" exception.
 * If the block does not throw but any of the objects throw during closing, injects a dummy exceptions and adds all
 * exceptions to it.
 */
inline fun <T : Closeable?, R> Iterable<T>.use(block: (Iterable<T>) -> R): R {
    var blockE: Throwable? = null
    try {
        return block(this)
    } catch (e: Throwable) {
        blockE = e
        throw e
    } finally {
        var dummyE: Exception? = null
        forEach {
            try {
                it?.close()
            } catch (closeE: Throwable) {
                if (blockE == null) {
                    if (dummyE == null) {
                        dummyE = Exception("Exception during closing")
                    }
                    dummyE!!.addSuppressed(closeE)
                } else {
                    blockE.addSuppressed(closeE)
                }
            }
        }
        if (dummyE != null) {
            throw dummyE!!
        }
    }
}

/**
 * Takes a list of [literals] together with a smt query [baseQuery], and returns the subset of [literals] that
 * is defined using only function symbols and variables from the [baseQuery].
 */
fun filterUndefinedLiterals(literals: List<SmtExp>, baseQuery: SmtFormulaCheckerQuery) =
    literals.asSequence()
        .filter { exp ->
            CollectQualIds.collectQualIds(exp)
                .all { it.id in baseQuery.variables }
        }
        .filter { exp ->
            CollectFunctionSymbols.collectFuncSymbols(exp)
                .filterNot { it.isBooleanConnective() || it.isBoolAtomWhenApplied() || it is SmtIntpFunctionSymbol }
                .all { baseQuery.symbolTable.hasFunDecl(it.name.toString()) }
        }

/**
 * Interface for a worker: [Closeable] (to get rid of the solver process) and a [run] method.
 */
interface AbstractWorker : Closeable {
    suspend fun run(): RaceFinish<SmtFormulaCheckerResultWithChecker>

    val name: String
}

/**
 * A generic solver class. Manages creation, model construction and destruction of the underlying solver.
 * If [dumpId] is given, the whole communication with the solver is written to a dump file.
 */
abstract class BaseSolver(
    val solverConfig: SolverConfig,
    val query: SmtFormulaCheckerQuery,
) : Closeable {
    lateinit var cmdProcessor: CmdProcessor
    lateinit var queryProcessor: SmtQueryProcessor

    protected suspend fun initialize(
        script: FactorySmtScript,
        unsatCores: Boolean,
        incremental: Boolean = true,
        dumpId: String? = null,
    ) {
        val finalLogic = if (solverConfig.solverInfo.needsLogicALL(query.logic.toSolverConfigLogicFeatures())) {
            Logic.ALL
        } else {
            query.logic
        }
        val solverInstanceInfo = SolverInstanceInfo.fromSolverConfig(
            solverConfig,
            CmdProcessor.Options.fromQuery(query, incremental = incremental).copy(
                logic = finalLogic,
                produceUnsatCores = unsatCores
            )
        )
        val dumpFile = if (dumpId == null) {
            null
        } else {
            var res: String? = null
            ArtifactManagerFactory().registerArtifact("dump-${dumpId}-${query.logic}.smt2", StaticArtifactLocation.Formulas) {
                res = it
            }
            res
        }
        cmdProcessor = ExtraCommandsCmdProcessor.fromSolverInstanceInfo(solverInstanceInfo, dumpFile = dumpFile)
        queryProcessor = SmtQueryProcessor(
            initialScript = script,
            name = solverInstanceInfo.name,
            cmdProcessor = cmdProcessor
        )
        query.assertFormulaSmtLines(queryProcessor.script).forEach {
            queryProcessor.process(it)
        }
    }

    /**
     * Obtain the model. Should only be called immediately after a SAT result.
     */
    suspend fun getModel(): Map<SmtExp, SmtExp> =
        queryProcessor.getValue(query.termsOfInterest.toList(), query.symbolTable)

    /**
     * Close the command processor, i.e. the solver process.
     */
    override fun close() {
        cmdProcessor.close()
    }
}

/**
 * Maintains a queue of candidate models (i.e. candidate counterexamples) that implements some logic to be clever about
 * allocating checking them to different solvers.
 */
class LIAModelQueue {
    enum class SolvingStatus {
        STARTED,
        FAILED,
        REFUTED,
    }

    private val nextModelID: AtomicInteger = AtomicInteger(1)

    /**
     * A candidate model (i.e. counterexample) with some metadata. Most importantly, stores the current solving status
     * for all solvers.
     */
    class LIAModel(
        val id: Int,
        val model: Map<SmtExp, SmtExp>,
        val relaxations: Int,
    ) {
        val status: MutableMap<Int, SolvingStatus> = mutableMapOf()

        /**
         * Checks if the candidate model can be removed from the queue: if it was refuted and no solver is currently
         * working on it.
         */
        fun isRemovable(): Boolean {
            if (status.containsValue(SolvingStatus.STARTED)) {
                return false
            }
            return status.containsValue(SolvingStatus.REFUTED)
        }
    }

    /**
     * The actual queue.
     */
    private val queue: Queue<LIAModel> = LinkedList()

    /**
     * Adds a new candidate model to the queue.
     * May be relaxed up to [CEGARConfig.WorkerConfig.niaRelaxations] times.
     */
    fun add(model: Map<SmtExp, SmtExp>, relaxations: Int = 0) {
        synchronized(queue) {
            queue.add(LIAModel(nextModelID.getAndIncrement(), model, relaxations))
        }
    }

    /**
     * Retrieve the next candidate model to be checked by the given [solver].
     * Returns a model that has not yet been checked by this [solver] and has neither been refuted nor taken by another
     * solver.
     */
    fun getNext(solver: Int): LIAModel? {
        return synchronized(queue) {
            queue.firstOrNull {
                !it.status.containsKey(solver) && !it.status.containsValue(SolvingStatus.REFUTED) && !it.status.containsValue(
                    SolvingStatus.STARTED
                )
            }
        }
    }

    /**
     * Updates the status of a [solver] on a [model]. Either [solver] has [STARTED] working on it (temporarily blocking
     * it to avoid work duplication), [REFUTED] it (permanently disabling it and possibly removing it from the queue
     * altogether) or [FAILED] doing so.
     */
    fun setStatus(solver: Int, model: LIAModel, result: SolvingStatus) {
        when (result) {
            SolvingStatus.STARTED -> model.status[solver] = result
            SolvingStatus.FAILED,
            SolvingStatus.REFUTED ->
                synchronized(queue) {
                    model.status[solver] = result
                    if (model.isRemovable()) {
                        queue.removeIf { it.id == model.id }
                    }
                }
        }
    }
}
