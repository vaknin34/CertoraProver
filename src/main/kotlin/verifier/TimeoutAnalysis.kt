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

package verifier

import analysis.CmdPointer
import config.Config
import datastructures.stdcollections.*
import log.*
import report.dumps.UnsolvedSplitInfo
import smt.SmtExpWithLExp
import smtlibutils.cmdprocessor.*
import smtlibutils.data.SmtScript
import solver.SolverConfig
import solver.SolverResult
import tac.NBId
import utils.mapNotNullToSet
import utils.mapToSet
import vc.data.CoreTACProgram
import vc.data.lexpression.META_TOPLVL_CMD
import verifier.splits.LazySubProgram
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds


private val logger = Logger(LoggerTypes.SMT_TIMEOUT)

data class UnsolvedSplit(
    val prog: CoreTACProgram,
    val smtRes: SmtFormulaCheckerResult.Single.Simple,
)

/** mapping back from smt expressions to tac commands using the meta entries (where present). */
val CoreHelper.coreAsTACCmds get() =
    coreAsHasSmtExps.mapNotNullToSet {
        val lexp = (it as? SmtExpWithLExp)?.lexp
        if (lexp == null) { logger.trace { "failed to get LExpression for smt exp \"$it\"" } }
        val meta = lexp?.meta
        if (meta == null) { logger.debug { "failed to get meta for smt exp \"$it\"" } }
        meta?.get(META_TOPLVL_CMD)
    }

/**
 * Takes an unsolved (due to timeout) split and attempts to isolate the timeout's root cause using CVC5's
 * (get-timeout-core) feature.
 */
object TimeoutCoreAnalysis {

    /** This formula is based on some experience, but generally very roundabout .. should we make that a config
     * option?? */
    private val timeoutCoreGlobalTimeout =
        maxOf(
            Config.SolverTimeout.get() * 10L,
            Config.TimeoutCoreTimeout.inWholeSeconds * 10,
            120L,
        ).seconds

    private fun getSolverConfig(timeoutCoreTimeout: Duration) =
        SolverConfig.cvc5.def.copy(
            variantName = "timeoutCore",
            clOptions = listOf(
                "--timeout-core-timeout=${timeoutCoreTimeout.inWholeMilliseconds}",
                "--tlimit=${timeoutCoreGlobalTimeout.inWholeMilliseconds}"
            ),
            timelimit = null, // switches off `--tlimit-per`
            customBinary = "cvc5-1.0.6-dev.225.c2dd8fe18",
        )

    class TimeoutCoreInfo(val coreAsCmdPtrs: Set<CmdPointer>) {
        val timeoutCoreBlocks: Set<NBId> = coreAsCmdPtrs.mapToSet { it.block }

        companion object {
            suspend fun compute(finalResult: SolverResult, unsolvedSplits: Set<UnsolvedSplit>): TimeoutCoreInfo? {
                return if (Config.TimeoutCores.get() && finalResult == SolverResult.TIMEOUT) {
                    if (unsolvedSplits.size > 1) {
                        logger.warn { "got more than one timing-out split -- only computing timeout core for the first one" }
                    }
                    @Suppress("SwallowedException", "TooGenericExceptionCaught")
                    val timeoutCoreInfo = try {
                        val res = analyzeUnsolvedSplit(unsolvedSplits.first(), Config.TimeoutCoreTimeout)
                        logger.debug { "timeout core computation finished without exception" }
                        res
                    } catch (e: Exception) {
                        logger.warn(e) { "timeout core computation threw an exception" }
                        null
                    }
                    logger.trace { "timeout core: ${timeoutCoreInfo?.timeoutCoreBlocks}"}
                    timeoutCoreInfo
                } else {
                    null
                }
            }
        }
    }

    /**
     * Main entry point of this class. See [TimeoutCoreAnalysis] for elaboration on the purpose.
     *
     * Steps:
     *  - run cvc5 to get timeout core
     *  - parse the result to map it back to tac commands
     *  - output the information in a format convenient for coloring the tac graph
     */
    suspend fun analyzeUnsolvedSplit(unsolvedSplit: UnsolvedSplit, timeoutCoreTimeout: Duration): TimeoutCoreInfo {
        require(unsolvedSplit.smtRes.hasTimeout) {
            "expecting a smt result that indicates a timeout, got \"${unsolvedSplit.smtRes}\""
        }

        /*
         * run CVC5 with
         *  - (get-timeout-core) instead of check-sat
         *  - `:produce-unsat-cores` smtlib option set
         *  - Not: `--print-unsat-cores-full` cli option (will be --no-print-use-names soon, apparently) (we use UnsatCoreHelper)
         *  - `--timeout-core-timeout=N` cli option set (no `--tlimit-per`)
         *  - ... and of course the split VC formula
         */
        val originalQuery = unsolvedSplit.smtRes.query
        val script = SmtScript(originalQuery.symbolTable)
        val cmdProcOptions = CmdProcessor.Options.Default.copy(produceUnsatCores = true)
        val coreHelper = CoreHelper(originalQuery.smtFormula.conjunction, script)
        val query = originalQuery.copy(coreHelper = coreHelper)


        logger.info { "starting timeout core computation (via cvc5), global timeout for that task: " +
            "${timeoutCoreGlobalTimeout.inWholeSeconds} seconds" }

        val ucAsCmdPtrs =
            SmtQueryProcessor.fromSolverInstanceInfo(
                SolverInstanceInfo.fromSolverConfig(
                    getSolverConfig(timeoutCoreTimeout),
                    cmdProcOptions,
                ),
                script,
                dumpFile = ArtifactManagerFactory().getFilePathForSmtQuery("timeoutCoreQp", subdir = null)
            ).use { qp ->
                // Feed the new query to the solver.
                query.assertFormulaSmtLines(script).forEach { cmd -> qp.process(cmd) }
                qp.getTimeoutCore(coreHelper)
                coreHelper.coreAsTACCmds
            }
        logger.debug { "got timeout core from solver (tac cmds): $ucAsCmdPtrs" }

        return TimeoutCoreInfo(ucAsCmdPtrs)
    }
}


/**
 * Local data structure for collecting timeout-related information ("unsolved splits" and "timeout core").
 * Meant to be constructed, filled, and consumed in [TACVerifier.leinoVCWithSplitting].
 */
internal class UnsolvedSplitData(
    val fullTimeOutBlocks: MutableSet<NBId> = mutableSetOf(),
    val mediumTimeOutBlocks: MutableSet<NBId> = mutableSetOf(),
    /** This is only filled if [Config.TimeoutCores] is set in order to save memory. */
    val unsolvedSplits: MutableSet<UnsolvedSplit> = mutableSetOf(),
) {

    /** track the "unsolved nodes" for the "UnsolvedSplits" graph coloring */
    fun registerFullTimeout(tac: CoreTACProgram, smtFormulaCheckerResult: SmtFormulaCheckerResult) {
        tac.analysisCache.graph.blocks.forEach { fullTimeOutBlocks += it.id }
        val singleSimple =
            smtFormulaCheckerResult.representativeResult as? SmtFormulaCheckerResult.Single.Simple
        if ((Config.TimeoutCores.get() || Config.getTimeoutCracker()) && singleSimple != null) {
            unsolvedSplits += UnsolvedSplit(tac, singleSimple)
        }
    }

    /** track the splits that we did not attempt to solve on the last split level */
    fun registerNotYetSolved(unsolved: Iterable<LazySubProgram>) {
        unsolved.forEach { split ->
            split.actualGraph().keys.forEach { mediumTimeOutBlocks += it }
        }
    }

    /** Convert to [UnsolvedSplitInfo], which is used to communicate the information outside of TACVerifier. */
    suspend fun toUnsolvedSplitInfo(tacProgram: CoreTACProgram, finalResult: SolverResult): UnsolvedSplitInfo =
        UnsolvedSplitInfo(
            fullTimeOutBlocks,
            mediumTimeOutBlocks,
            tacProgram,
            TimeoutCoreAnalysis.TimeoutCoreInfo.compute(finalResult, unsolvedSplits),
        )

}

