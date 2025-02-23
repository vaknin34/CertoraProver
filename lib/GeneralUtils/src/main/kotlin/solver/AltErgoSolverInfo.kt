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

import log.*
import kotlin.time.Duration

object AltErgoSolverInfo: SolverInfo(name = "Alt-Ergo") {
    private val logger = Logger(GeneralUtilsLoggerTypes.SOLVERCONFIG)
    private const val DEFAULT_ALT_ERGO_COMMAND = "alt-ergo"

    // note: there is also the --timelimit-per-goal option, but it's unclear to me if that applies to SMT mode of Alt-Ergo
    override fun getOptionForTimelimit(timelimit: Duration): List<String> = listOf("--timelimit=${timelimit.inWholeSeconds}")

    // actually not sure what alt-ergo supports -- setting to true for now
    override fun supportsLogicFeatures(features: SolverConfig.LogicFeatures): Boolean = true

    override fun getOptionForIncremental(): List<String> {
        throw UnsupportedOperationException("support of incremental mode by Alt-Ergo (in SMT-mode) is unclear (might investigate)")
    }
    override fun getOptionForRandomSeed(randomSeed: Int): List<String> {
        logger.warn { "AltErgo does not support changing the random seed (tried to set it to $randomSeed)" }
        return listOf()
    }

    override fun commandForStdInMode(clOptions: List<String>, customBinary: String?): List<String> {
        return listOf(customBinary ?: DEFAULT_ALT_ERGO_COMMAND, "--input=smtlib2") + clOptions
    }

    override val defaultCommand: String
        get() = DEFAULT_ALT_ERGO_COMMAND

    private fun readResolve(): Any = AltErgoSolverInfo
}
