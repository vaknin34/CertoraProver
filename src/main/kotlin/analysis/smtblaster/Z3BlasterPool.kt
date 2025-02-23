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

package analysis.smtblaster

import config.Config
import log.ArtifactManagerFactory
import log.*
import parallel.coroutines.onThisThread
import smtlibutils.cmdprocessor.*
import smtlibutils.data.Cmd
import smtlibutils.data.FactorySmtScript
import smtlibutils.data.SatResult
import solver.SolverConfig
import java.io.Closeable
import kotlin.time.Duration
import java.util.concurrent.*
import java.util.concurrent.atomic.AtomicInteger
import kotlin.time.Duration.Companion.milliseconds

private val pLogger = Logger(GeneralUtilsLoggerTypes.PARALLEL)

class Z3BlasterPool(
    private val workers: Int = System.getProperty("cvt.default.parallelism")?.toIntOrNull() ?: Runtime.getRuntime()
        .availableProcessors(),
    z3TimeoutMs: Int = 500,
    private val solverConfig: SolverConfig = SolverConfig.z3.default,
    private val fallbackSolverConfig: SolverConfig? = null,
    poolName: String = "blasterPool",
) : IBlaster, Closeable {
    private data class Query(
        val query: SmtFormulaCheckerQuery,
        val result: CompletableFuture<Pair<Boolean, Boolean>>
    )

    private val uniquePoolName = "${poolName}_${poolCtr.incrementAndGet()}"

    private val solverTimeout = FORCE_Z3_TIMEOUT ?: z3TimeoutMs.milliseconds

    private val options = CmdProcessor.Options.BareBonesIncremental
    private val script = FactorySmtScript

    companion object {
        var FORCE_Z3_TIMEOUT: Duration? = null

        /** Used to disambiguate the (default) names of different [Z3BlasterPool] instances. */
        val poolCtr: AtomicInteger = AtomicInteger(0)
    }

    private val channel = SynchronousQueue<Query>()

    private val workerPool = Executors.newFixedThreadPool(2 * workers + 1)

    init {
        start()
    }

    private inner class Z3BlasterWorker(val name: String) : Runnable {
        private val checker = setupFormulaChecker(!Config.ShouldDeleteSMTFiles.get())

        private fun setupFormulaChecker(logToFile: Boolean = false): SmtFormulaChecker = onThisThread {
            val dumpFile =
                if (logToFile) {
                    ArtifactManagerFactory().getFilePathForSmtQuery(name, IBlaster.BLASTERS_SUBDIR_NAME)
                } else {
                    null
                }

            /* To clarify: When we have a fallback solver, the inner solvers don't dump, instead the outer,
             * SequentialFormulaChecker does.  */

            val primaryChecker = (SimpleFormulaChecker.singleCheckerSpawnerFromSolverInfoOrNull(
                SolverInstanceInfo(
                    solverConfig.copy(
                        timelimit = solverTimeout,
                        memlimitBytes = null,
                    ),
                    options = options,
                    critical = true
                ),
                script,
                if (fallbackSolverConfig == null) dumpFile?.let { "$it.smt2" } else null
            ) ?: error("failed to spawn solverProcess $solverConfig"))()

            if (fallbackSolverConfig != null) {
                val fallbackChecker = (SimpleFormulaChecker.singleCheckerSpawnerFromSolverInfoOrNull(
                    SolverInstanceInfo(
                        fallbackSolverConfig.copy(
                            timelimit = solverTimeout.times(2), // double the timeout for fallbacks
                            memlimitBytes = null,
                        ),
                        options = options,
                        critical = true
                    ),
                    script,
                    null
                ) ?: error("failed to spawn solverProcess $fallbackSolverConfig"))()

                SmtFormulaChecker.sequential(
                    script,
                    options,
                    listOf(primaryChecker, fallbackChecker),
                    dumpFile?.let { "$it.smt2" })
            } else {
                primaryChecker
            }
        }


        override fun run() {
            while (true) {
                val x = try {
                    channel.take()
                } catch (e: InterruptedException) {
                    shutdown()
                    return
                }
                pLogger.debug {
                    "Running command in thread ${Thread.currentThread()}"
                }
                check(x is Query)


                try {
                    val result = onThisThread { checker.check(x.query) }
                    x.result.complete(
                        Pair(
                            result.satResult == SatResult.UNSAT,
                            result.satResult is SatResult.UNKNOWN
                        )
                    )
                } catch (e: Exception) {
                    if(this@Z3BlasterPool.timeoutShutdown) {
                        x.result.complete(false to true)
                        return
                    }
                    x.result.completeExceptionally(e)
                }
            }

        }

        private fun shutdown() {
            checker.close()
        }
    }

    private fun start() {
        for (i in 0..workers) {
            workerPool.submit(Z3BlasterWorker("${uniquePoolName}_worker_$i"))
        }
    }

    override fun close() {
        workerPool.shutdownNow()
        workerPool.awaitTermination((solverTimeout.inWholeMilliseconds + 100), TimeUnit.MILLISECONDS)
    }

    @Volatile
    private var timeoutShutdown : Boolean = false


    private fun timeoutShutdownAndThrow() {
        if(!timeoutShutdown) {
            synchronized(this) {
                if(!timeoutShutdown) {
                    timeoutShutdown = true
                    workerPool.shutdownNow()
                }
            }
        }
        throw IBlaster.SmtTimeoutError()
    }

    fun submit(query: List<Cmd>): Pair<Boolean, Boolean> {
        val queryName = "blasterPoolQuery"

        pLogger.debug {
            "About to submit and stall in thread ${Thread.currentThread()}"
        }
        val container = CompletableFuture<Pair<Boolean, Boolean>>()
        val smtFormula = SmtFormula.fromSmt(script.smt(query))
        try {
            val res = workerPool.submit(Runnable {
                channel.put(
                    Query(
                        SmtFormulaCheckerQuery(SmtFormulaCheckerQueryInfo(queryName), smtFormula),
                        container
                    )
                )
            })
            res.get()
        } catch(x: RejectedExecutionException) {
            if(IBlaster.FAIL_ON_TIMEOUT && timeoutShutdown) {
                throw IBlaster.SmtTimeoutError()
            } else {
                throw x
            }
        }
        val (unsat, timeout) = container.get()
        if (timeout && IBlaster.FAIL_ON_TIMEOUT) {
            this.timeoutShutdownAndThrow()
        }
        return unsat to timeout
    }

    override fun blastSmt(vc_query: List<Cmd>): Boolean = submit(vc_query).first

    // returns (unsat, timeout) to give timeout information in addition
    override fun blastSmtOrTimeout(vc_query: List<Cmd>): Pair<Boolean, Boolean> = submit(vc_query)
}
