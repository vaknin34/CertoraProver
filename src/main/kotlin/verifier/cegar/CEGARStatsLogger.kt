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

import smt.ConstraintChooserEnum
import smtlibutils.data.SatResult
import smtlibutils.data.SmtExp
import solver.SolverConfig
import statistics.ScalarKeyValueStats
import statistics.SDCollectorFactory
import statistics.toSDFeatureKey
import kotlin.time.Duration
import java.time.LocalDateTime
import java.time.format.DateTimeFormatter

class CEGARStatsLogger {

    enum class LogEntryType {
        ExactNIA, LIA, NIA
    }

    private data class LogEntry(
        val queryName: String,
        val type: LogEntryType,
        val sc: SolverConfig,
        val duration: Duration,
        val completionTime: LocalDateTime,
        val result: SatResult,
        val cc: ConstraintChooserEnum?,
        val cex: List<SmtExp>?,
    )

    private val logEntries = mutableListOf<LogEntry>()

    fun log(
        queryName: String,
        type: LogEntryType,
        sc: SolverConfig,
        duration: Duration,
        completionTime: LocalDateTime = LocalDateTime.now(),
        result: SatResult,
        cc: ConstraintChooserEnum?,
        cex: List<SmtExp>?,
    ) =
        logEntries.add(LogEntry(queryName, type, sc, duration, completionTime, result, cc, cex))

    /**
     * This method should be called when all stats have been collected. It registers those stats in our statistics
     * infrastructure (statsdata.json).
     */
    fun registerStats() {
        logEntries.forEachIndexed { id,e ->
            val kvl = ScalarKeyValueStats<String>(e.queryName.toSDFeatureKey(), "CEGAR".toSDFeatureKey(), "$id".toSDFeatureKey())
            kvl.addKeyValue("type", "${e.type}")
            kvl.addKeyValue("solver-name", "${e.sc.fullName}")
            kvl.addKeyValue("solver-binary", "${e.sc.solverInfo.defaultCommand}")
            kvl.addKeyValue("command-line", "${e.sc.getCommandline().joinToString(" ")}")
            when (e.result) {
                is SatResult.SAT -> kvl.addKeyValue("result", "sat")
                is SatResult.UNSAT -> kvl.addKeyValue("result", "unsat")
                is SatResult.UNKNOWN -> {
                    kvl.addKeyValue("result", "unknown")
                    kvl.addKeyValue("unknown-reason", e.result.reason.toString())
                    e.result.infoString?.let { kvl.addKeyValue("unknown-error", it) }
                }
            }
            kvl.addKeyValue("completion", e.completionTime.format(DateTimeFormatter.ISO_LOCAL_DATE_TIME))
            kvl.addKeyValue("duration", "${e.duration.inWholeMilliseconds}ms")
            e.cex?.let { kvl.addKeyValue("cex-size", "${it.size}") }
            e.cc?.let { kvl.addKeyValue("cchooser", it.name) }
            SDCollectorFactory.collector().collectFeature(kvl)
        }
    }
}
