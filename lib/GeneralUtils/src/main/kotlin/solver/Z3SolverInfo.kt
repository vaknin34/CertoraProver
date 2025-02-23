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

package solver

import datastructures.stdcollections.*
import kotlin.time.Duration


object Z3SolverInfo : SolverInfo(name = "Z3") {
    private val alwaysOnOptions = listOf<String>()

    override fun getOptionForTimelimit(timelimit: Duration): List<String> = listOf("-t:${timelimit.inWholeMilliseconds}")

    //the '5' in 'smt.phase_selection=5' means `random` phase selection
    override fun getOptionForRandomSeed(randomSeed: Int): List<String> = listOf(
                    "smt.random_seed=$randomSeed",
                    "sat.random_seed=$randomSeed",
    )

    override fun getCmdToChangeTimelimit(timelimit: Duration) = "(set-option :timeout ${timelimit.inWholeMilliseconds})"

    override fun supportsLogicFeatures(features: SolverConfig.LogicFeatures): Boolean = true

    override val supportsNewSmtLibBvOverflowSymbols get() = true

    /**
     * z3 rejects `DT` logics.
     * (It prints "unsupported logic" on things like QF_UFDTLIA and then continues using the ALL logic, which then
     *  handles the formula correctly.)
     */
    override fun needsLogicALL(features: SolverConfig.LogicFeatures): Boolean =
        features.usesDatatypes

    private const val DEFAULT_Z3_COMMAND = "z3"

    override fun commandForStdInMode(clOptions: List<String>, customBinary: String?): List<String> =
        listOf(customBinary ?: DEFAULT_Z3_COMMAND, "-in") + alwaysOnOptions + clOptions

    override val defaultCommand: String
        get() = DEFAULT_Z3_COMMAND


    fun plainConfig(timelimit: Duration, incrementalMode: Boolean = false): SolverConfig =
        SolverConfig.z3.default.copy(timelimit = timelimit, incremental = incrementalMode)

    private fun readResolve(): Any = Z3SolverInfo
}
