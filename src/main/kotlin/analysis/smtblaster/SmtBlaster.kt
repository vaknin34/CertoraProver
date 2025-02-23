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
import log.Logger
import log.LoggerTypes
import parallel.coroutines.onThisThread
import smtlibutils.cmdprocessor.*
import smtlibutils.data.Cmd
import smtlibutils.data.FactorySmtScript
import smtlibutils.data.SatResult
import solver.*
import solver.SolverInfo
import solver.Z3SolverInfo
import kotlin.time.Duration
import java.util.concurrent.atomic.AtomicInteger
import kotlin.time.Duration.Companion.milliseconds

private val logger = Logger(LoggerTypes.BIT_BLAST)

open class SmtBlaster(
    private val name: String,
    private val solverConfig: SolverConfig,
    private val solverInfo: SolverInfo,
    private val timeout: Duration,
) : IBlaster {
    private val uniqueBlasterName = "${name}_${blasterCtr.incrementAndGet()}"

    fun querySmt(
        formula: SmtFormula,
        termsOfInterest: TermsOfInterest
    ): SmtFormulaCheckerResult {
        val uniqueQueryName = "query_${queryCtr.incrementAndGet()}"

        val options = CmdProcessor.Options.BareBonesIncremental.copy(
            produceModels = termsOfInterest !is EmptyTermsOfInterest
        )

        val script = FactorySmtScript

        val solverInstanceInfo =
            SolverInstanceInfo(solverConfig.copy(timelimit = timeout), options)

        val dumpFile =
            if (!Config.ShouldDeleteSMTFiles.get()) {
                ArtifactManagerFactory().getFilePathForSmtQuery(
                    "${uniqueBlasterName}_${uniqueQueryName}",
                    IBlaster.BLASTERS_SUBDIR_NAME
                )
            } else {
                null
            }

        val checker: suspend () -> SmtFormulaChecker = SimpleFormulaChecker.singleCheckerSpawnerFromSolverInfoOrNull(
            solverInstanceInfo,
            script,
            dumpFile = dumpFile
        ) ?: error("failed to spawn instance of $solverInfo")

        val query = SmtFormulaCheckerQuery(
            SmtFormulaCheckerQueryInfo(uniqueQueryName),
            formula,
            termsOfInterest = termsOfInterest
        )

        return onThisThread { checker().use { it.check(query) } }
    }

    override fun blastSmtOrTimeout(vc_query: List<Cmd>): Pair<Boolean, Boolean> {
        logger.trace {
            "Sending query for verification\n$vc_query"
        }

        val formula = SmtFormula.fromSmt(FactorySmtScript.smt(vc_query))
        val result = querySmt(formula, EmptyTermsOfInterest)

        return when (result.satResult) {
            is SatResult.SAT -> false to false
            is SatResult.UNKNOWN -> false to true
            SatResult.UNSAT -> true to false
        }
    }

    companion object {
        val blasterCtr: AtomicInteger = AtomicInteger(0)
        val queryCtr: AtomicInteger = AtomicInteger(0)
    }
}

object Z3Blaster : SmtBlaster("z3Blaster", SolverConfig.z3.default, Z3SolverInfo, 500.milliseconds)
