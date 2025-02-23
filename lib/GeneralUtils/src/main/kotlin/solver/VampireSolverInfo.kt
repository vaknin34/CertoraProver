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

object VampireSolverInfo: SolverInfo(name = "Vampire") {
    private const val DEFAULT_VAMPIRE_COMMAND = "vprover"

    override fun getOptionForIncremental(): List<String> {
        throw UnsupportedOperationException("incremental mode is not supported by Vampire")
    }

    override fun getOptionForTimelimit(timelimit: Duration): List<String> =
        listOf("--time_limit", "${timelimit.inWholeSeconds}")
    override fun getOptionForRandomSeed(randomSeed: Int): List<String> = listOf("--random_seed $randomSeed")

    // actually not sure what vampire supports -- setting to true for now
    override fun supportsLogicFeatures(features: SolverConfig.LogicFeatures): Boolean = true

    /**
     * not so nice to first multiply then later divide by 1000, it's due to different conventions btw solvers,
     * should not hurt either as long as we don't care for time limit differences that are less than a second..
     */
    override fun commandForStdInMode(clOptions: List<String>, customBinary: String?): List<String> {
        /*
           --mode smtcomp doesn't respect the time limit and core limit, apparently, so we're going for:
           --input_syntax smtlib2 --mode portfolio --schedule smtcomp --cores 1 --output_mode smtcomp
           old stuff:
            RuntimeEnvInfo.getTimeoutCommand(timeoutSeconds) +
            listOf(customSolverCommand ?: DEFAULT_VAMPIRE_COMMAND, "--mode", "smtcomp", "--cores", "1") +
         */

        return listOf(
            customBinary ?: DEFAULT_VAMPIRE_COMMAND,
            "--input_syntax",
            "smtlib2",
            "--mode",
            "portfolio",
            "--schedule",
            "smtcomp",
            "--cores",
            "1",
            "--output_mode",
            "smtcomp"
        ) + clOptions
    }

    override val defaultCommand: String
        get() = DEFAULT_VAMPIRE_COMMAND

    private fun readResolve(): Any = VampireSolverInfo
}

