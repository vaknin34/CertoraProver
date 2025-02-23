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

package smtlibutils.statistics

import parallel.ParallelPool
import parallel.Scheduler
import parallel.pcompute
import parallel.coroutines.onThisThread
import smtlibutils.cmdprocessor.*
import smtlibutils.data.FindLogic
import smtlibutils.data.Logic
import smtlibutils.data.SatResult
import smtlibutils.parser.SMTParser
import smtlibutils.statistics.CollectDifficultyStats.SmtFileStats.Companion.FILENAME
import utils.getCurrentTime
import java.io.File
import java.io.FileReader
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds
import utils.*

private typealias DataRow = Map<String, Any?>

/**
 * Contains methods and data structures to collect statistical information about a collection of smt files.
 * Can either dump the results as a `.csv` or print them to the terminal.
 */
object CollectDifficultyStats {

    data class SmtFileStats(
        val file: File,
        val logic: Logic,
        val runtime: Duration?,
        val satResult: SatResult?,
        val counters: List<CollectStatsCmdProc.CounterData>
    ) {
        companion object {
            const val FILENAME = "filename"
            const val LOGIC = "logic"
            const val RUNTIME = "z3_time_(sec)"
            const val SATRESULT = "satResult"
        }

        val headers
            get() = setOf(
                FILENAME,
                LOGIC,
                RUNTIME,
                SATRESULT
            ) + counters.flatMapTo(mutableSetOf()) { it.headers }

        fun asDataRow(): DataRow {
            val res = mutableMapOf<String, Any?>()
            res[FILENAME] = file.toString()
            res[LOGIC] = logic.toString()
            res[RUNTIME] = runtime?.inWholeSeconds.toString()
            res[SATRESULT] = satResult?.toString()
            counters.forEach { c ->
                c.entryToCounter.forEach { (e, c) ->
                    res[e] = c
                }
            }
            return res
        }


        @Deprecated("keeping this for a short time in case some code snippets can be cannibalized")
        fun asDataRow(allHeaders: List<String>): DataRow =
            allHeaders.associate { header ->
                when (header) {
                    FILENAME -> FILENAME to file.toString()
                    LOGIC -> LOGIC to logic.toString()
                    else -> {
                        val entry = counters.firstNotNullOfOrNull { c -> c.entryToCounter[header]?.toString() }
                        header to entry
                    }
                }
            }
    }


    /**
     * Collect statistics on [smtFiles].
     * If [outputCsvFile] is null, will print a summary to the terminal, otherwise will dump to that file in csv format.
     * Will add solver statistics to the collected stats if [runZ3] is true. Will use [solverTimeout] as the solver
     * timeout.
     */
    fun collectStats(
        outputCsvFile: File?,
        smtFiles: List<File>,
        runZ3: Boolean = true,
        solverTimeout: Duration = 15.seconds,
    ) {
        val smtFileStats = mutableListOf<SmtFileStats>()

        val parallelJobs = smtFiles.map { smtFile ->
            Scheduler.compute {
                val parser = FileReader(smtFile).use { f ->
                    val parser = SMTParser(f.readText())
                    parser.parse()
                    parser
                }

                val smt = parser.getSmt()
                val logic = FindLogic.findLogic(smt)
                val counters = onThisThread { CollectStatsCmdProc.countSmt(smt) }

                Triple(
                    parser.getSmtScript(),
                    smt,
                    SmtFileStats(
                        smtFile,
                        logic,
                        null, // runTime,
                        null, // checkRes?.satResult,
                        counters.map { it.toCounterData() })
                )
            }.bind { (script, smt, stats) ->
                rpc {
                    val (runTime, checkRes) =
                        if (runZ3) {
                            println("start z3 on $smtFile")
                            val startTime = getCurrentTime()
                            val query = SmtFormulaCheckerQuery(SmtFormulaCheckerQueryInfo("q", statistics = QueryStatistics()), SmtFormula.fromSmt(smt))
                            onThisThread {
                                SimpleFormulaChecker.plainZ3Instance(solverTimeout, script, dumpFile = null).use { sfc ->
                                    try {
                                        val checkRes: SmtFormulaCheckerResult =
                                            sfc.check(query) as SmtFormulaCheckerResult.Single.Simple
                                        println("z3 finished on $smtFile with ${checkRes.satResult}")
                                        println()
                                        startTime.elapsedNow() to checkRes
                                    } catch (e: Exception) {
                                        print("z3 crashed")
                                        val runTime = startTime.elapsedNow()
                                        runTime to SmtFormulaCheckerResult.ProcessDied(e, sfc, query)
                                    }
                                }
                            }
                        } else {
                            null to null
                        }
                    stats.copy(runtime = runTime, satResult = checkRes?.satResult)
                }
            }

        }

        ParallelPool.runInherit(parallelJobs.pcompute(), ParallelPool.SpawnPolicy.GLOBAL)

        smtFileStats.addAll(parallelJobs.pcompute().result)

        val headers = smtFileStats.flatMapTo(mutableSetOf()) { it.headers }.toList()
        val rows = smtFileStats.map { it.asDataRow() }
        if (outputCsvFile != null) {
            outputCsvFile.bufferedWriter().use { writer ->
                fun csvEncode(value: Any?) = value?.toString()?.let { s ->
                    s.letIf(s.any { it == '"' || it == ',' || it == '\n' }) {
                        "\"${s.replace("\"", "\"\"")}\""
                    }
                }.orEmpty()
                writer.write(headers.joinToString(",") { csvEncode(it) })
                writer.newLine()
                rows.forEach { row ->
                    writer.write(headers.joinToString(",") { csvEncode(row[it]) })
                    writer.newLine()
                }
            }
            print("wrote to ${outputCsvFile.absoluteFile}")
        } else {
            rows.forEach { row ->
                println(row[FILENAME])
                row.keys.filter { it != FILENAME }.forEach { column ->
                    println("  $column:  ${row[column]}")
                }
            }
        }
    }
}
