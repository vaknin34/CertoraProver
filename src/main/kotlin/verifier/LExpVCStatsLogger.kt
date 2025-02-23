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

import smtlibutils.cmdprocessor.SmtFormulaCheckerResult
import smtlibutils.data.SatResult
import statistics.ScalarKeyValueStats
import statistics.SDCollectorFactory
import statistics.toSDFeatureKey
import kotlin.time.Duration
import kotlin.time.Duration.Companion.milliseconds
import datastructures.stdcollections.*
import smtlibutils.statistics.ExecutableStatistics
import java.util.*


/**
 * A logger for SMT results, integrating with main statistics infrastructure.
 */
class LExpVCStatsLogger {

    private data class LogEntry(
        val exec: Executable,
        val timeout: Duration,
        val result: SmtFormulaCheckerResult.Single?,
    )

    private val logEntries = mutableListOf<LogEntry>()

    private var numAllLearnedClauses: Int = 0
    private var numUsableLearnedClauses: Int = 0

    fun log(
        exec: Executable,
        timeout: Duration,
        result: SmtFormulaCheckerResult.Single?,
    ) =
        logEntries.add(LogEntry(exec, timeout, result))

    fun logProducedLearnedClauses(all: Int, usable: Int) {
        numAllLearnedClauses = all
        numUsableLearnedClauses = usable
    }

    /**
     * This method should be called when all stats have been collected. It registers those stats in our statistics
     * infrastructure (statsdata.json).
     */
    fun registerStats() {
        /**
         * It stores results under the following heirarchy
         *
         * <parentJob> corresponds to a bunch of solvers that were started in parallel on the same smt problem,
         *   which was encoded in the theory <theory>, this may look like this "ParallelVJob#8234893-UFLIA".
         *
         * <queryName> : {
         *    <race-description>[timeout=<timeout>] : {
         *       "SAT" : <list of solver commands, including cli options>
         *       "UNSAT" : <list of solver commands, including cli options>
         *       "never got to run" : "*" for each solver that never got to run because the race was already done
         *       others : solver finished because of some other reason (e.g., was stopped in the middle because the race was done
         *    }
         * }
         */
        logEntries
            .reversed() // so order corresponds to time (not sure this actually helps)
            .groupBy { e -> Triple(e.exec.query.info.name, e.exec.raceDescription, e.timeout) }
            .forEach { (triple, entries) ->
                val (queryName, raceDescription, timeout) = triple
                val kvl = ScalarKeyValueStats<String>(
                    queryName.toSDFeatureKey(), // ruleName
                    "${raceDescription.toSDFeatureKey()}[timeout=${timeout.inWholeSeconds}s]".toSDFeatureKey(), // raceDescription+timeout
                )
                entries.forEach { e ->
                    val cmd = e.exec.checkerInstance?.solverInstanceInfo?.actualCommand
                    val resultStr = getResultStr(e.result?.satResult) { if (cmd == null) "NotCreated" else "LostRace" }

                    kvl.addKeyValue(
                        resultStr,
                        "${e.exec.config.fullName}, ${cmd?.joinToString(" ") ?: ""}[${e.exec.timeUsed ?: 0}ms]"
                    )
                }
                SDCollectorFactory.collector().collectFeature(kvl)
            }
    }

    companion object {
        fun getResultStr(r: SatResult?, getStringIfNullResult: () -> String = { "Not specified "}) =
            when (r) {
                null -> getStringIfNullResult()
                is SatResult.UNKNOWN -> r.reason.toString()
                else -> r.toString()
            }
        /**
         * Given a [SmtFormulaCheckerResult], return the list of its race nodes.
         *
         * For a discussion on the result tree and statistics, see `SmtFormulaCheckerResult.kt`.
         *
         * The following code only assumes that the input is a tree.  In particular, it will go to an infinite loop with
         * structures that have non-trivial loops where a node can be reached again by following more than one edge.
         *
         * A result's race labeling is ok if every rooted path to a leaf passes through exactly one race node.
         * @return `null` if the race labeling is not ok; otherwise return the result nodes that have a non-null
         * `raceInfo` field.
         */
        private fun getRaceNodes(result: SmtFormulaCheckerResult): List<SmtFormulaCheckerResult>? {
            class IntHolder(var i: Int)

            val stack = ArrayDeque<Pair<SmtFormulaCheckerResult, IntHolder>>()
            var ok = true
            val okNodeSet = mutableSetOf<SmtFormulaCheckerResult>()
            val raceNodeList = mutableListOf<SmtFormulaCheckerResult>()
            stack.push(Pair(result, IntHolder(0)))
            while (stack.isNotEmpty()) {
                val (res, procChildren) = stack.first
                if (!ok) {
                    stack.pop()
                    continue
                }
                // In some types result is its own subresult.
                // prettification results are not subject to the path condition on race labeling
                val subResults = res.subResults.filterNot { res === it }
                val numChildren = subResults.size

                if (procChildren.i < numChildren) {
                    stack.push(Pair(subResults[procChildren.i++], IntHolder(0)))
                    continue
                }
                val numOkChildren = subResults.count { okNodeSet.contains(it) }
                val allChildrenOk = (numOkChildren == numChildren)
                val hasOkChild = numOkChildren > 0
                val isOkNode = ((hasOkChild && allChildrenOk) || (res.raceInfo != null))
                if (isOkNode) { okNodeSet.add(res) }
                if (hasOkChild && !allChildrenOk) {
                    // The node has an ok child and a non-ok child.  Either
                    //  1. the non-ok child has a rooted path that does not pass through a race node, or
                    //  2. the ok child has a rooted path that passes through two race nodes
                    ok = false
                }
                if (hasOkChild && res.raceInfo != null) {
                    // The okChild has a rooted path that passes through two race nodes
                    ok = false
                }
                if (res.raceInfo != null) { raceNodeList.add(res) }

                stack.pop()
            }
            return if (ok && okNodeSet.contains(result)) { raceNodeList } else { null }
        }

        fun resultToRaceStatistics(result: SmtFormulaCheckerResult): List<RaceStatistic>? {

            val raceNodes = getRaceNodes(result) ?: return null

            val toSingleResultStatistic: (ExecutableStatistics) -> SingleResultStatistic =
                { stat ->
                    SingleResultStatistic(
                        satResult = getResultStr(stat.satResult),
                        logic = stat.queryStats?.logic.toString(),
                        solverConfigurationName = stat.preExecutionStatistics?.configStats?.solverConfigurationName.toString(),
                        solverName = stat.preExecutionStatistics?.configStats?.solverName.toString(),
                        arguments = stat.preExecutionStatistics?.configStats?.arguments.toString(),
                        solvingTime = stat.resultStats?.solverWallRuntime ?: 0.milliseconds,
                        smtGenerationTime = stat.queryStats?.axiomStatistics?.smtGenerationTime,
                        vcGenerationTime = stat.queryStats?.axiomStatistics?.vcGenerationTime,
                        learnedClauseParsingTime = stat.queryStats?.learnedClauseParsingTime,
                        learnedClauseInputNum = stat.queryStats?.learnedClauseInputNum,
                        learnedClauseUsableNum = stat.queryStats?.learnedClauseUsableNum,
                        learnedClauseOutputNum = stat.resultStats?.learnedClauseOutputNum ?: 0,
                        execTimeToStartSinceJarStart = stat.resultStats?.startTime,
                        execThreadName = stat.resultStats?.threadName
                    )
                }
            val nodeGroups = raceNodes.groupBy { it.raceInfo!!.id } // all results in raceNodes must by definition have non-null raceInfo
            // We sort races by raceId, so they appear in the run order in statsdata.
            return nodeGroups.keys.sorted().map { raceId ->
                val nodes = nodeGroups[raceId]!! // nodeGroups[raceId] must be non-null since raceId is a key
                require(nodes.isNotEmpty()) // groupBy must return a non-empty list for each key
                val raceInfo = nodes[0].raceInfo!! // The raceInfo of a race node cannot be null
                val listOfSingleResultStatisticsForRace = nodes.map { it.collectStatistics() }.flatten().map { toSingleResultStatistic(it) }

                RaceStatistic(
                    timeout = raceInfo.timeout,
                    raceDescription = raceInfo.raceDescription,
                    solvingTime = raceInfo.runTime,
                    timeToStartSinceJarStart = raceInfo.startTime,
                    singleResults = listOfSingleResultStatisticsForRace
                )
            }
        }
    }
}

