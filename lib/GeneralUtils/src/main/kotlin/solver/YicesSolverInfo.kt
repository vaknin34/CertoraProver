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

import kotlin.time.Duration

object YicesSolverInfo: SolverInfo(name = "Yices") {
    private const val DEFAULT_YICES_COMMAND = "yices-smt2"

    override fun getOptionForIncremental(): List<String> = listOf("--incremental")
    override fun getOptionForTimelimit(timelimit: Duration): List<String> = listOf("--timeout=${timelimit.inWholeSeconds}")
    override fun getCmdToChangeTimelimit(timelimit: Duration) = "(set-option :timeout ${timelimit.inWholeSeconds})"

    /**
     * note: incremental mode can hurt performance it seems, so should only be used when necessary
     *
     *
     * also: not so nice to first multiply then later divide by 1000, it's due to different conventions btw solvers,
     * should not hurt either as long as we don't care for time limit differences that are less than a second..
     */
    override fun commandForStdInMode(clOptions: List<String>, customBinary: String?): List<String> =
        listOf(customBinary ?: DEFAULT_YICES_COMMAND, "--interactive") + clOptions

    override val defaultCommand: String
        get() = DEFAULT_YICES_COMMAND

    override fun supportsLogicFeatures(features: SolverConfig.LogicFeatures): Boolean {
        if (features.usesDatatypes) {
            return false
        }
        return true
    }

    private fun readResolve(): Any = YicesSolverInfo
}
