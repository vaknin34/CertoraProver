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

package verifier.autoconfig


import kotlinx.serialization.Serializable
import solver.SolverChoice
import datastructures.stdcollections.*
import log.Logger
import log.LoggerTypes
import smtlibutils.data.Logic

enum class BaseLogic {
    NIA, LIA, UNKNOWN;

    companion object {
        fun fromLogic(logic: Logic) = when(val ao = logic.arithmeticOperations) {
            Logic.ArithmeticOperations.LinearOnly -> LIA
            Logic.ArithmeticOperations.NonLinear -> NIA
            else -> {
                Logger(LoggerTypes.AUTOCONFIG).warn { "The given logic does not match any BaseLogic: $ao" }
                UNKNOWN
            } // TODO CERT-3998: support also BV
        }
    }
}

@Serializable
data class SolverId(val name: String, val logic: BaseLogic)

/**
 * Maintains the statistics about a particular solver configuration, identified by [id], across
 * all already processed splits.
 */
class SingleSolverConfigStats(val id: SolverId) {
    private val resultCounts = mutableMapOf<String, Int>()
    var usefulResults = 0
    private var uselessResults = 0
    var losts = 0
    private val numOfResults: Int get() = usefulResults + uselessResults
    fun addResult(res: String, raceHasWinner: Boolean) {
        resultCounts[res] = resultCounts.getOrDefault(res, 0) + 1
        if (BasicSplitStatistics.isUsefulSolverResult(res)) {
            usefulResults += 1
        } else {
            uselessResults += 1
            if (raceHasWinner) {
                losts += 1
            }
        }
    }

    fun usefulness() = if (numOfResults == 0) {
        1.0
    } else {
        usefulResults.toDouble() / numOfResults
    }
}

/**
 * Maintains statistics about individual solver configurations (via [addResult]) and proposes configurations
 * that should be used (via [getPrioritisedLIAConfigs] and [getPrioritisedNIAConfigs]).
 */
class SolverConfigsStats {
    private val configs = mutableMapOf<SolverId, SingleSolverConfigStats>()

    init {
        SolverChoice.LIASolversMediumTimeout.forEach {
            val solverId = SolverId(it.fullName, BaseLogic.LIA)
            configs[solverId] = SingleSolverConfigStats(solverId)
        }
        SolverChoice.NIASolversMediumTimeout.forEach {
            val solverId = SolverId(it.fullName, BaseLogic.NIA)
            configs[solverId] = SingleSolverConfigStats(solverId)
        }
    }

    fun addResult(id: SolverId, res: String, raceHasWinner: Boolean) =
        configs.getOrPut(id) { SingleSolverConfigStats(id) }.addResult(res, raceHasWinner)

    private fun getPrioritisedSolverNames(
        configs: Map<SolverId, SingleSolverConfigStats>,
        numOfSCToTake: Int = 4,
        maxNumOfLosts: Int = 2,
    ): List<String> {
        //We pick a solver config iff i] it lost at most [maxNumOfLosts] or ii] it was already useful
        return configs.filter { (it.value.losts <= maxNumOfLosts || it.value.usefulResults > 0) }
            .values.sortedByDescending { it.usefulness() }
            .take(numOfSCToTake)
            .map { it.id.name }
    }

    fun getPrioritisedLIAConfigs(numOfSCToTake: Int = 4)
        = getPrioritisedSolverNames(configs.filter { it.key.logic == BaseLogic.LIA }, numOfSCToTake)
    fun getPrioritisedNIAConfigs(numOfSCToTake: Int = 4)
        = getPrioritisedSolverNames(configs.filter { it.key.logic == BaseLogic.NIA }, numOfSCToTake)
}
