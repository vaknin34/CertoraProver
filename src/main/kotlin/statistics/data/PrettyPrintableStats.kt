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

import kotlinx.serialization.Serializable
import log.*
import report.LiveCheckInfoNode
import tac.CallId
import utils.HasKSerializable


private val logger = Logger(LoggerTypes.SMT_TIMEOUT)

sealed interface PrettyPrintableStats : HasKSerializable {
    /** Short string version of the stats. */
    val asText: String

    /** Text that is displayed on top level in the Live Stats tab in the report for this stat. */
    val liveStatsSummaryText: String

    /** Roughly indicates whether the difficulty stats should be concerning or not. */
    val severityGlobal: Severity

    fun severityPerCall(callId: CallId): Severity = Severity.UNKNOWN

    /** Indicates how severe the given difficulty stat's values are, in our experience.
     * E.g. for global path count the mapping is like this (actual values subject to change)
     *   <2^20  ~> LOW
     *   <2^100  ~> MEDIUM
     *   else   ~> HIGH
     * .
     * They roughly translate like this:
     *  LOW    ~> most likely least concern (any timeouts likely aren't due to this)
     *  MEDIUM ~> perhaps a concern, perhaps not (timeouts might be due to this, perhaps in combination with other things)
     *  HIGH   ~> most likely a concern (this alone is likely to lead to a timeout)
     */
    enum class Severity(val asHtmlReportSeverity: Int, val asHtmlReportHeuristicSeverity: Int) {
        UNKNOWN(0, 0),
        LOW(1, 0),
        MEDIUM(2, 0),
        HIGH(3, 1),
    }
}

fun <T : PrettyPrintableStats> List<T>.emptyOrSingleOrPickFirst(): T? =
    when (this.size) {
        0 -> null
        1 -> this.single()
        else -> {
            logger.debug { "got more than one stat for the same object (full list: $this) -- expecting all to be " +
                "the same, so just picking the first" }
            this.first()
        }
    }

/**
 * @param graphSize number of nodes in the array graph
 */
@Serializable
data class ArrayGeneratorStats(
    val graphSize: Int?,
    val longestStoreChainLength: Int?,
    val opCount: Map<String, Int>?
) : PrettyPrintableStats {
    class Builder {
        var graphSize: Int? = null
        var longestStoreChainLength: Int? = null
        var opCount: Map<String, Int>? = null
        fun build() =
            ArrayGeneratorStats(
                graphSize ?: run {
                    logger.warn { "no graph size reported by array generator" }
                    null
                },
                longestStoreChainLength ?: run {
                    logger.warn { "no store chain length reported by array generator" }
                    null
                },
                opCount ?: run {
                    logger.warn { "no operation counts reported by array generator" }
                    null
                },
            )
    }

    override val asText get() =
        "Memory/Storage: Graph Size: $graphSize; Longest Path Length: $longestStoreChainLength; " +
            "OpCounts: { ${opCount?.entries?.joinToString(separator = ", ") { (k, v) -> "$k : $v" } } }"

    override val liveStatsSummaryText get() =
        "memory updates: $graphSize\nlongest update sequence: $longestStoreChainLength"

    override val severityGlobal: PrettyPrintableStats.Severity
        get() = when {
            graphSize == null -> PrettyPrintableStats.Severity.UNKNOWN
            // really unsure about these numbers... need some more data
            graphSize < 50 -> PrettyPrintableStats.Severity.LOW
            graphSize < 500 -> PrettyPrintableStats.Severity.MEDIUM
            else -> PrettyPrintableStats.Severity.HIGH
        }

    fun toTreeViewFormat(): LiveCheckInfoNode {
        val asHtmlReportSeverity = this.severityGlobal.asHtmlReportSeverity
        return LiveCheckInfoNode.keyValue(
            label = "memory complexity",
            value = liveStatsSummaryText,
            severity = asHtmlReportSeverity,
            link = LiveStats.highMemComplexityLink.takeIf { asHtmlReportSeverity > 1 },
        )
    }
}

@Serializable
data class BitwiseAxiomGeneratorStats(
    val bwands: Int,
    val bwors: Int,
    val bwxors: Int,
    val signExtends: Int,
): PrettyPrintableStats {
    class Builder {
        var bwands: Int = 0
        var bwors: Int = 0
        var bwxors: Int = 0
        var signExtends: Int = 0
        fun build() = BitwiseAxiomGeneratorStats(bwands, bwors, bwxors, signExtends)
    }

    override val asText get() =
        "Bitwise Op Counts: BwAnd: $bwands BwOr: $bwors BwXor: $bwxors SignExtend: $signExtends"

    // NB this is not displayed in the live stats as of now, so this is unused (having something in case we accidentally display it for now)
    override val liveStatsSummaryText: String
        get() = asText

    override val severityGlobal: PrettyPrintableStats.Severity
        get() = PrettyPrintableStats.Severity.UNKNOWN // these stats need some more attention ...
}
