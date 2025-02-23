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

import smtlibutils.data.SatResult
import solver.ConfigStatistics
import utils.TimeSinceStart
import kotlin.time.Duration

class LearnedClausesFilterStatistics (
    val numUsableLearnedClauses: Int = 0, // Learned clauses that were usable on a given logic
    val numAllLearnedClauses: Int = 0, // All available learned clauses before filtering based, e.g., on VC
)


class AxiomStatistics(
    val smtGenerationTime: Duration? = null,
    val vcGenerationTime: Duration? = null,
)

class QueryStatistics(
    val logic: String? = null,
    val axiomStatistics: AxiomStatistics = AxiomStatistics(),
    val learnedClauseParsingTime: Duration? = null,
    val learnedClauseInputNum: Int? = null,
    val learnedClauseUsableNum: Int? = null,
)

class PreExecutionStatistics(
    val configStats: ConfigStatistics,
    val preprocessorStatistics: List<ExecutableStatistics>?,
)

class ResultStatistics(
    val learnedClauseOutputNum: Int? = null,
    val solverWallRuntime: Duration? = null,
    val solverCPURuntime: Duration? = null,
    val startTime: TimeSinceStart? = null,
    val threadName: String? = null,
)

class ExecutableStatistics(
    val queryStats: QueryStatistics?,
    val preExecutionStatistics: PreExecutionStatistics?,
    val resultStats: ResultStatistics? = ResultStatistics(),
    val satResult: SatResult,
)
