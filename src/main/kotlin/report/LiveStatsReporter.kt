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

package report

import datastructures.stdcollections.*
import kotlinx.serialization.json.JsonArray
import log.*
import report.dumps.CallGraphInfo
import spec.cvlast.RuleIdentifier
import statistics.data.LiveStats
import statistics.data.LiveStats.Companion.toTreeViewFormat
import statistics.data.LiveStatsProgressInfo
import statistics.data.SingleDifficultyStats
import java.util.concurrent.atomic.AtomicInteger

private val logger = Logger(LoggerTypes.SMT_TIMEOUT)

data class LiveCheckData(
    val nodes: List<LiveCheckInfoNode>,
    val progress: Int?,
) {
    fun toJSON(): String {
        val asTreeViewRep = this.nodes.map(TreeViewReportable::toTreeViewRep)
        return JsonArray(asTreeViewRep).toString()
    }
}

/**
 * Live stats are reported to this.
 * This reports those stats to the html report through [TreeViewReporter] (on each `hotUpdate()` call therein).
 *
 * Note that there is only one instance of this around at any time, that instance is registered as a field in
 * [TreeViewReporter].
 */
sealed interface LiveStatsReporter {
    fun reportDifficulty(rule: RuleIdentifier, callGraphInfo: CallGraphInfo, stats: SingleDifficultyStats)
    fun reportProgress(rule: RuleIdentifier, stats: LiveStatsProgressInfo)
    val ruleToLiveCheckData: Map<RuleIdentifier, LiveCheckData>

}

object DummyLiveStatsReporter : LiveStatsReporter {
    private fun info(stats: LiveStats): String =
        "not reporting live stats for program \"${stats.ruleAndSplitId.ruleId}\" to " +
        "treeViewReporter because DummyLiveStatsReporter is active"
    override fun reportDifficulty(rule: RuleIdentifier, callGraphInfo: CallGraphInfo, stats: SingleDifficultyStats) {
        logger.info { info(stats) }
    }
    override fun reportProgress(rule: RuleIdentifier, stats: LiveStatsProgressInfo) {
        logger.info { info(stats) }
    }
    override val ruleToLiveCheckData: Map<RuleIdentifier, LiveCheckData> = emptyMap()
}

class ConcreteLiveStatsReporter : LiveStatsReporter {
    // for debugging -- displays how often `hotUpdateLiveCheckInfo` was called in the live check info tab
    private val hotUpdateLciCounter = AtomicInteger(0)

    private val collectedLiveStats: MutableMap<RuleIdentifier, MutableList<LiveStats>> =
        mutableMapOf()
    private val ruleToCallGraph: MutableMap<RuleIdentifier, CallGraphInfo?> =
        mutableMapOf()

    override fun reportDifficulty(rule: RuleIdentifier, callGraphInfo: CallGraphInfo, stats: SingleDifficultyStats) {
        synchronized(this) {
            if (rule !in ruleToCallGraph) {
                ruleToCallGraph[rule] = callGraphInfo
            }
            collectedLiveStats.getOrPut(rule) { mutableListOf() }.add(stats)
        }
    }

    override fun reportProgress(rule: RuleIdentifier, stats: LiveStatsProgressInfo) {
        logger.info { "report progress for rule: $rule; type: ${stats.javaClass.simpleName}" }
        synchronized(this) {
            collectedLiveStats.getOrPut(rule) { mutableListOf() }.add(stats)
        }
    }

    /** Brings the current state of the live stats into a json-ish form as a map from rule to [LiveCheckInfoNode]s. */
    override val ruleToLiveCheckData: Map<RuleIdentifier, LiveCheckData>
        get() =
            synchronized(this) {
                collectedLiveStats.mapValues { (rule, stats) ->
                    val liveCheckInformation =
                        stats.toTreeViewFormat(
                            hotUpdateLciCounter.getAndIncrement(),
                            ruleToCallGraph[rule],
                        )

                    val splitProgressPercentage = stats.filterIsInstance<LiveStatsProgressInfo>()
                        .maxByOrNull { it.compareId }?.splitProgressPercentage

                    LiveCheckData(
                        liveCheckInformation,
                        splitProgressPercentage,
                    )
                }
            }

    companion object {
        /** display an update counter in the live stats (just displays that the last update to the stats was the n-th)
         * -- for debugging purposes */
        const val DISPLAY_UPDATE_COUNTER: Boolean = false
    }
}
