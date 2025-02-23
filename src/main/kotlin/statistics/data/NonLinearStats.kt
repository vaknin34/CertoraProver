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

package statistics.data

import analysis.*
import datastructures.MutableMultiMap
import datastructures.add
import datastructures.mutableMultiMapOf
import datastructures.stdcollections.*
import kotlinx.serialization.Serializable
import log.*
import report.dumps.BlockDifficulty
import report.dumps.CountDifficultOps
import report.dumps.Difficulty
import tac.CallId
import utils.*
import vc.data.*
import verifier.CodeAnalysis


private val logger = Logger(LoggerTypes.SMT_TIMEOUT)

/**
 * Statistics about how "heavy" hte nonlinear math in a TAC program is.
 *
 * Note that the stats in [perCallId] are not cumulative with respect to deeper calls, i.e., if `foo` calls `bar`, and
 * `bar` has nonlinear operations, they are not counted towards the nonlinear operations of `bar` here
 * (the path count in [PathCountStats] works differently in that respect).
 */
@Serializable
data class NonLinearStats(
    val global: Data,
    val perCallId: List<Pair<CallIdWithName, Data>>?,
    val procIdToNlOpCountScore: Map<String, Int>,
    val procIdToPolyDegScore: Map<String, Int>,
): PrettyPrintableStats {
    constructor(
        highestDegree: Int?,
        numberOfNonlinearOps: Int?,
        perCallIdCounter: List<Pair<CallIdWithName, Int>>?,
        procIdToNlOpCountScore: Map<String, Int>,
        procIdToPolyDegScore: Map<String, Int>,
    ):
        this(
            Data(highestDegree, numberOfNonlinearOps),
            perCallIdCounter?.map { (callId, nlOpsCount) -> callId to Data(null, nlOpsCount) },
            procIdToNlOpCountScore,
            procIdToPolyDegScore,
        )


    val highestDegree get() = global.highestDegree
    val numberOfNonlinearOps get() = global.numberOfNonlinearOps

    @Serializable
    class Data(val highestDegree: Int?, val numberOfNonlinearOps: Int?) {
        override fun toString(): String =
            listOfNotNull(highestDegree?.let { deg -> "polynomial degree: $deg " },
                numberOfNonlinearOps?.let { nlOps -> "nonlinear ops: $nlOps" }).joinToString("\n")
    }


    val perCallIdCounterAsMap: Map<CallId, Data>? by lazy { perCallId?.map { it.first.callId to it.second }?.toMap() }

    override val asText get() =
        listOfNotNull(
            "Nonlinearity:",
            highestDegree?.let { "Max Polynomial Degree: $it" },
            numberOfNonlinearOps?.let { "nonlinear ops: $it" }
        ).joinToString(" ")

    val nlOpsText get() =
        numberOfNonlinearOps?.let { "nonlinear ops: $it" }

    val polyDegreeText get() =
        highestDegree?.let { "max polyn. degree: $it" }

    override val severityGlobal: PrettyPrintableStats.Severity
        get() =
            numberOfNonlinearOps.let { nlOps -> // to allow for the smartcast ...
                when {
                    (nlOps == null) -> PrettyPrintableStats.Severity.UNKNOWN
                    nlOps < 5 -> PrettyPrintableStats.Severity.LOW
                    nlOps < 30 -> PrettyPrintableStats.Severity.MEDIUM
                    else -> PrettyPrintableStats.Severity.HIGH
                }
            }

    override fun severityPerCall(callId: CallId): PrettyPrintableStats.Severity {
        val perCall = perCallIdCounterAsMap?.get(callId)?.numberOfNonlinearOps
        return when {
            perCall == null -> PrettyPrintableStats.Severity.UNKNOWN
            perCall < 1 -> PrettyPrintableStats.Severity.LOW
            perCall < 4 -> PrettyPrintableStats.Severity.MEDIUM
            else -> PrettyPrintableStats.Severity.HIGH
        }
    }

    override val liveStatsSummaryText get() =
        listOfNotNull(nlOpsText, polyDegreeText).joinToString(separator = "\n")

    fun asLongText(lineSeparator: String = "<br/>\n") =
        if (perCallId != null) {
            highestDegree?.let { "Max Polynomial Degree: $it$lineSeparator" }.orEmpty() +
            "Detailed nonlinear op count info:$lineSeparator" +
                perCallId.joinToString(lineSeparator) { (callId, nlOpCount) ->
                    "$callId: $nlOpCount"
                }
        } else {
            "detailed nonlinear op count info not available"
        }

    companion object {

        /** hard-coded setting for the dataflow-based nonlinearity analysis */
        private const val computePolynomialDegree = true // compute it at all
        private const val dataFlowsThroughMaps: Boolean = true // true/false: everything/nothing may alias
        private const val divAndModSum: Boolean = false // true/false: handle div and mod like multiplication/addition

        /**
         * Compute nonlinearity stats for given program [prog].
         *
         * @param callIdNames meta info for [prog]: the names for the [CallId]s occuring in the program
         * @param doDataFlowAnalysis whether to perform [PolydegAnalysis] aka. "polynomial degree"
         * @param dataFlowsThroughMaps see [PolydegAnalysis]
         * @param divAndModSum see [PolydegAnalysis]
         */
        fun computeAndLogTime(
            prog: CoreTACProgram,
            callIdNames: Map<Int, String>?,
            computeProcedureHotspots: Boolean,
        ): NonLinearStats =
            CodeAnalysis(
                analysisName = "NonLinearStats",
                analyzer = { it: CoreTACProgram ->
                    compute(it, callIdNames, computeProcedureHotspots, computePolynomialDegree, dataFlowsThroughMaps, divAndModSum)
                },
                successCriteria = { true }
            ).runAnalysis(prog)

        // public only for unit tests
        fun compute(
            prog: CoreTACProgram,
            callIdNames: Map<Int, String>?,
            computeProcedureHotspots: Boolean = true,
            doDataFlowAnalysis: Boolean = true,
            dataFlowsThroughMaps: Boolean = true,
            divAndModSum: Boolean = false,
        ): NonLinearStats {
            val procedureIdToCallIds = mutableMultiMapOf<ProcedureId, CallId>().apply {
                prog.procedures.forEach { procedure ->
                    add(procedure.procedureId, procedure.callId)
                }
            }

            // compute polynomial degree related stats
            val highestDegree = if (doDataFlowAnalysis) {
                val analysis = PolydegAnalysis(
                    prog = prog,
                    callIdsToJump = null,
                    dataFlowsThroughMaps = dataFlowsThroughMaps,
                    divAndModSum = divAndModSum
                )
                analysis.go()
                analysis.maxDegree
            } else {
                null
            }

            // compute nonlinear operation count related stats
            val countDifficultOps = CountDifficultOps(prog)
            val perCallIdCounter = mutableMapOf<CallIdWithName, Int>().apply {
                prog.blockgraph.keys.forEach { blockId ->
                    val calleeIdx = blockId.calleeIdx
                    val res: BlockDifficulty? = countDifficultOps[blockId]
                    val nlOpsCount = res?.getOccurrenceCount { it.difficulty == Difficulty.NonLinearity }
                    if (nlOpsCount != null && nlOpsCount != 0) {
                        updateInPlace(
                            CallIdWithName(calleeIdx, callIdNames?.get(calleeIdx).orEmpty()),
                            default = 0
                        ) { callId ->
                            callId + nlOpsCount
                        }
                    }
                }
            }
            val globalCounter = perCallIdCounter.values.sum()
            val procIdToNlOpCountScore =
                if (computeProcedureHotspots) {
                    procedureIdToCallIds.entries.associate { (procId, callIds) ->
                        val countWithout = perCallIdCounter.filterKeys { it.callId !in callIds }.values.sum()
                        val score = computePercentageScore(globalCounter, countWithout)
                        procId to score
                    }
                } else {
                    emptyMap()
                }

            return NonLinearStats(
                highestDegree,
                globalCounter,
                perCallIdCounter.toList().sortedBy { it.first.callId },
                procIdToNlOpCountScore.mapKeys { (k, _) -> k.toString() },
                if (computeProcedureHotspots) {
                    computeProcIdToPolyDegreeScore(
                        prog,
                        procedureIdToCallIds,
                        highestDegree,
                        dataFlowsThroughMaps,
                        divAndModSum,
                    ).mapKeys { (k, _) -> k.toString() }
                } else {
                    emptyMap()
                }
            )
        }


        private fun computeProcIdToPolyDegreeScore(
            prog: CoreTACProgram,
            procedureIdToCallIds: MutableMultiMap<ProcedureId, CallId>,
            globalMaxDegree: Int?,
            dataFlowsThroughMaps: Boolean,
            divAndModSum: Boolean
        ): Map<ProcedureId, Int> {
            if (globalMaxDegree == null) {
                logger.warn {
                    "failed to compute global max. polynomial degree, cannot compute per-procedure " +
                        "nonlinear difficulty scores"
                }
                return emptyMap()
            }

            return procedureIdToCallIds.entries.associate { (procedureId, callIds) ->
                val analysis = PolydegAnalysis(
                    prog = prog,
                    callIdsToJump = callIds,
                    dataFlowsThroughMaps = dataFlowsThroughMaps,
                    divAndModSum = divAndModSum
                )
                analysis.go()
                val maxDegree = analysis.maxDegree
                val score = computePercentageScore(globalMaxDegree, maxDegree)
                // println("------- $procedureId ~~> glob: $globalMaxDegree jumped: $maxDegree score: $score")
                procedureId to score
            }
        }

        private fun computePercentageScore(global: Int, globalWithout: Int) =
            if (global == 0) {
                0
            } else {
                ((global - globalWithout) * 100) / global
            }
    }
}
