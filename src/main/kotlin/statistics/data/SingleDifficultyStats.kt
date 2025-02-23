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


import algorithms.topologicalOrder
import analysis.worklist.volatileDagDataFlow
import datastructures.stdcollections.*
import kotlinx.serialization.Serializable
import kotlinx.serialization.encodeToString
import kotlinx.serialization.json.Json
import report.LiveCheckInfoNode
import report.TreeViewLocation
import report.dumps.CallGraphInfo
import tac.CallId
import tac.NBId
import utils.*
import verifier.RuleAndSplitIdentifier


/**
 * Difficulty stats that are reported from a single code location (e.g. axiom generation, or "right before splitting",
 * etc).
 */
@Serializable
sealed class SingleDifficultyStats : HasKSerializable, Comparable<SingleDifficultyStats>, LiveStats {

    abstract val stats: List<PrettyPrintableStats>

    override fun compareTo(other: SingleDifficultyStats): Int = compareId - other.compareId

    val statsAsText get() = stats.joinToString("\n") { it.asText }

    @KSerializable
    data class TacProgramStats(
        override val ruleAndSplitId: RuleAndSplitIdentifier,
        val pathCountStats: PathCountStats?,
        val nonLinearStats: NonLinearStats?,
        val loopStats: LoopStats?,
    ) : SingleDifficultyStats() {
        override val compareId: Int = LiveStats.compareCounter.incrementAndGet()

        override val stats: List<PrettyPrintableStats>
            get() = listOfNotNull(pathCountStats, nonLinearStats)

        override fun toString(): String {
            return json.encodeToString(this)
        }

        companion object {
            private val json = Json { prettyPrint = true }

            private const val calleesLabel = "callees"


            fun List<TacProgramStats>.toTreeView(
                callGraphInfo: CallGraphInfo?
            ): Map<TopLevelLiveStats, LiveCheckInfoNode> {
                val callGraph = callGraphInfo?.callGraph

                val pathCountStats = this.mapNotNull { it.pathCountStats }.emptyOrSingleOrPickFirst()
                val nonLinearStats = this.mapNotNull { it.nonLinearStats }.emptyOrSingleOrPickFirst()
                val loopStats = this.mapNotNull { it.loopStats }.emptyOrSingleOrPickFirst()

                val nonLinearOpsPerCallIdCumulative = mutableMapOf<CallId, Int>().apply {
                    val nonLinearStatsPerCallId = nonLinearStats?.perCallIdCounterAsMap
                    callGraph?.let { callGraph ->
                        volatileDagDataFlow(callGraph) { node: CallId, successorResults: List<Int> ->
                            val nlOpsCount =
                                ((nonLinearStatsPerCallId?.get(node)?.numberOfNonlinearOps)
                                    ?: 0) + successorResults.sum()
                            put(node, nlOpsCount)
                            nlOpsCount
                        }
                    }
                }

                // true iff this node or any of its children is heuristically difficulty (according to nonlinear stats)
                val isAnyChildHeuristicallyDifficult = mutableMapOf<CallId, Boolean>()
                fun isAnyChildHeuristicallyDifficult(callId: CallId): Boolean =
                    isAnyChildHeuristicallyDifficult.computeIfAbsent(callId) {
                        if ((nonLinearStats?.severityPerCall(it)?.asHtmlReportHeuristicSeverity ?: 0) > 0) {
                            true
                        } else {
                            callGraph?.get(it)?.any { callee -> isAnyChildHeuristicallyDifficult(callee) } ?: false
                        }
                    }

                fun perCallNode(callId: CallId, children: List<LiveCheckInfoNode>) =
                    LiveCheckInfoNode.many(
                        label = callGraphInfo?.getCallIdWithName(callId).toString(),
                        children = listOfNotNull(
                            pathCountStats?.callIdToPathCountDataMap?.get(callGraphInfo?.getCallIdWithName(callId))?.asText
                                ?.let { text ->
                                    LiveCheckInfoNode.keyValue(
                                        label = "path count",
                                        value = text,
                                    )
                                },
                            LiveCheckInfoNode.keyValue(
                                label = "#nonlinear operations",
                                value = (nonLinearOpsPerCallIdCumulative[callId] ?: 0).toString()
                            ),
                            loopStats?.perCallId?.find { it.first == (callGraphInfo?.getCallIdWithName(callId)) }?.let {
                                LiveCheckInfoNode.keyValue(
                                    label = "longest loop",
                                    value = it.second.longestLoop.toString(),
                                )
                            },
                            loopStats?.perCallId?.find { it.first == (callGraphInfo?.getCallIdWithName(callId)) }?.let {
                                LiveCheckInfoNode.keyValue(
                                    label = "#loops",
                                    value = it.second.numberOfLoops.toString(),
                                )
                            },
                            if (children.isEmpty()) {
                                null
                            } else {
                                LiveCheckInfoNode.many(
                                    label = calleesLabel,
                                    children = children
                                )
                            }
                        ),
                        jumpToDefinition = callGraphInfo?.let { it.callIdToSourceLocation[callId] }
                            ?: TreeViewLocation.Empty,
                        severity = 0,
                        hSev = ite(isAnyChildHeuristicallyDifficult(callId), 1, 0)
                    )

                val callToVisNode = mutableMapOf<CallId, LiveCheckInfoNode>()
                if (callGraph != null) {
                    topologicalOrder(callGraph).forEach { callId ->
                        val childrenVisNodes = callGraph[callId]?.map { callToVisNode[it]!! }.orEmpty()
                        callToVisNode[callId] =
                            perCallNode(callId, childrenVisNodes)
                    }
                }

                return mapOf(
                    TopLevelLiveStats.globalPathCount to
                        (pathCountStats?.severityGlobal?.asHtmlReportSeverity ?: 0).let { severityAsInt ->
                            pathCountStats?.liveStatsSummaryText?.let { valueText ->
                                LiveCheckInfoNode.keyValue(
                                    label = "path count",
                                    value = valueText,
                                    severity = severityAsInt,
                                    link = LiveStats.highPathCountLink.takeIf { severityAsInt > 1 },
                                )
                            }
                        },
                    TopLevelLiveStats.globalNonlinearity to
                        (nonLinearStats?.severityGlobal?.asHtmlReportSeverity ?: 0).let { severityAsInt ->
                            nonLinearStats?.liveStatsSummaryText?.let { nlOpsText ->
                                LiveCheckInfoNode.keyValue(
                                    label = "nonlinearity",
                                    value = nlOpsText,
                                    severity = nonLinearStats.severityGlobal.asHtmlReportSeverity,
                                    link = LiveStats.highNonlinearOpsLink.takeIf { severityAsInt > 1 },
                                )
                            }
                        },
                    TopLevelLiveStats.globalLoops to
                        (loopStats?.severityGlobal?.asHtmlReportSeverity ?: 0).let { severityAsInt ->
                            if (severityAsInt >= PrettyPrintableStats.Severity.MEDIUM.asHtmlReportSeverity) {
                                loopStats?.liveStatsSummaryText?.let { valueText ->
                                    LiveCheckInfoNode.keyValue(
                                        label = "loop complexity",
                                        value = valueText,
                                        severity = loopStats.severityGlobal.asHtmlReportSeverity,
                                        link = LiveStats.highPathCountLink.takeIf { severityAsInt > 1 }, // long loops usually mean high path count
                                    )
                                }
                            } else {
                                null
                            }
                        },
                    TopLevelLiveStats.pathCountHotspots to
                        (pathCountStats?.procIdToDifficultyScore?.takeIf { isNotEmpty() }?.entries?.let { procIdToScore ->
                            LiveCheckInfoNode.many(
                                "path count hotspots",
                                children = run {
                                    val hotspotSorted = procIdToScore
                                        .filter { (_, v) -> v > 5f } // cutoff -- the "easy" ones are not shown
                                        .sortedByDescending { (_, v) -> v }

                                    hotspotSorted.map { (procId, score) ->
                                        LiveCheckInfoNode.keyValue(
                                            label = "function: $procId",
                                            value = "contrib. to branching: $score %",
                                            jumpToDefinition = callGraphInfo?.let {
                                                // not ideal, this lookup ... (but can't have ProcedureId be a key in
                                                // pcs.procIdToDifficultyScore due to serializability issues..)
                                                it.procIdToSourceLocation.findEntry { procedureId, _ ->
                                                    procedureId.toString() == procId
                                                }?.second
                                            } ?: TreeViewLocation.Empty,
                                        )
                                    }
                                }
                            )
                        }),

                    TopLevelLiveStats.nonlinearityHotspots to run {
                        if (nonLinearStats == null) {
                            return@run null
                        }
                        val procToNlOps = nonLinearStats.procIdToNlOpCountScore
                        val procToPolyDeg = nonLinearStats.procIdToPolyDegScore
                        val zipped = procToNlOps.zip(procToPolyDeg)
                        val hotspotsSorted = zipped.filter { (_, pair) ->
                            val (nlOps, polydeg) = pair
                            (nlOps != null && nlOps > 10) || (polydeg != null && polydeg > 5) // we can experiment with this cutoff..
                        }.sortedByDescending { (_, pair) ->
                            val (nlOps, polydeg) = pair
                            (nlOps ?: 0) + (polydeg ?: 0)
                        }
                        if (hotspotsSorted.isEmpty()) {
                            return@run null
                        }
                        LiveCheckInfoNode.many(
                            "nonlinearity hotspots",
                            children = run {

                                hotspotsSorted.map { (procId, pair) ->
                                    val (nlOps, polydeg) = pair
                                    LiveCheckInfoNode.keyValue(
                                        label = "function: $procId",
                                        value = listOfNotNull(
                                            nlOps?.let { x: Int -> "contrib. to nonlinear ops: $x %" },
                                            polydeg?.let { x: Int -> "contrib. to max polyn. degree: $x %" }).joinToString(
                                            separator = " \n"
                                        ),
                                        jumpToDefinition = callGraphInfo?.let {
                                            // not ideal, this lookup ... (but can't have ProcedureId be a key in
                                            // pcs.procIdToDifficultyScore due to serializability issues..)
                                            it.procIdToSourceLocation.findEntry { procedureId, _ ->
                                                procedureId.toString() == procId
                                            }?.second
                                        } ?: TreeViewLocation.Empty,
                                    )
                                }
                            }.toList()
                        )
                    },
                    TopLevelLiveStats.perCallStats to
                        LiveCheckInfoNode.many(
                            "per call stats",
                            children = if (
                                callToVisNode[NBId.ROOT_CALL_ID]?.children != null
                            ) {
                                callToVisNode[NBId.ROOT_CALL_ID]!!.children
                                    .find { it.label == calleesLabel }?.children.orEmpty() // go one level in, so we don't show the global stats again
                            } else {
                                listOf(
                                    LiveCheckInfoNode.onlyLabel(
                                        "failed to compute per-call stats"
                                    )
                                )
                            },
                        )
                ).mapValuesNotNull {
                    (_, v) -> v
                }
            }
        }
    }

    @KSerializable
    data class LExpToSmtLibstats(
        override val ruleAndSplitId: RuleAndSplitIdentifier,
        val queryName: String,
        val arrayGeneratorStats: ArrayGeneratorStats?,
        val bwAxiomStats: BitwiseAxiomGeneratorStats?,
    ) : SingleDifficultyStats() {
        override val compareId: Int = LiveStats.compareCounter.incrementAndGet()
        override val stats: List<PrettyPrintableStats>
            get() = listOfNotNull(arrayGeneratorStats, bwAxiomStats)
    }
}

