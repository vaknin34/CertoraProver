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

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import smtlibutils.cmdprocessor.*
import smtlibutils.data.*
import smtlibutils.statistics.PreExecutionStatistics
import solver.ConfigStatistics
import utils.TimeSinceStart
import kotlin.time.Duration.Companion.seconds

class SmtFormulaCheckerResultTest {
    @Test
    fun checkRaceLabeling() {
        val script = SmtScript()
        val solver = runBlocking { SimpleFormulaChecker.plainZ3Instance(10.seconds, script) }
        val query = SmtFormulaCheckerQuery(
            SmtFormulaCheckerQueryInfo(name = "test"),
            smtFormula = SmtFormula(Logic.ALL,
                script.symbolTable,
                listOf(),
                listOf(),
                listOf()
            )
        )
        val results =
            listOf(
                SatResult.UNSAT,
                SatResult.UNKNOWN(SatResult.UnknownReason.Timeout(null))
            ).map {
                SmtFormulaCheckerResult.Single.Simple(
                    (solver as SimpleFormulaChecker).solverInstanceInfo,
                    it,
                    null,
                    null,
                    query,
                    listOf(),
                    4.seconds,
                    null,
                    PreExecutionStatistics(ConfigStatistics("UnitTest"), listOf()),
                    null,
                )

            }

        var raceId = 0

        // Correct labeling: each rooted path passes through exactly one race-labeled result
        results.forEach { it.registerToRace(raceId++, "TestRace${raceId}", 4.seconds, 5.seconds, TimeSinceStart()) }
        val aggregate = SmtFormulaCheckerResult.Agg.LExpVcCheckerResult(results[0], listOf(results[1]))

        val raceStatistics = LExpVCStatsLogger.resultToRaceStatistics(aggregate)
        assertNotNull(raceStatistics) // Check that we produce a race
        assertEquals(2, raceStatistics!!.size) // There should be two races now
        raceStatistics.forEach { assertEquals(1, it.singleResults.size) } // Each race should have one singleResult


        // Incorrect labeling: a rooted path passes through two race-labeled result
        aggregate.registerToRace(raceId++, "RaceWithSubraces", 4.seconds, 5.seconds, TimeSinceStart())
        assertNull(LExpVCStatsLogger.resultToRaceStatistics(aggregate))

        // Incorrect labeling: a rooted path does not pass through a race-labeled result
        aggregate.raceInfo = null
        results[0].raceInfo = null
        assertNull(LExpVCStatsLogger.resultToRaceStatistics(aggregate))

    }
}
