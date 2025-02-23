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

import kotlinx.coroutines.flow.*
import kotlin.time.Duration

/**
 * Notes about options
 * -m : like adding (set-option :produce-models true) at the start and (get-model) at the end of the file
 *       --> we add those commands ourselves, so don't need the option
 * --time : overall timelimit (?) couldn't find a per-query time limit -- but we don't use the distinction much anyway, so
 *   should be ok for most cases and the main pipeline..
 */
object BitwuzlaSolverInfo: SolverInfo("Bitwuzla") {
    override val defaultCommand: String
        get() = "bitwuzla"

    override val supportsReset: Boolean = false

    override val supportsNewSmtLibBvOverflowSymbols get() = true

    override fun getOptionForIncremental(): List<String> = listOf()
    fun getProcessTimeoutString(timelimit: Duration): List<String> = listOf("--time-limit=${timelimit.inWholeMilliseconds}")

    override fun getOptionForTimelimit(timelimit: Duration): List<String> = getProcessTimeoutString(timelimit)

    override fun supportsLogicFeatures(features: SolverConfig.LogicFeatures): Boolean {
        if (features.usesDatatypes) {
            return false
        }
        if (features.arithmeticOperations in setOf(
                        ArithmeticOperations.NonLinear,
                        ArithmeticOperations.LinearOnly
                )
        ) {
            return false
        }
        return true
    }

    override fun commandForStdInMode(clOptions: List<String>, customBinary: String?): List<String> =
        listOf(customBinary ?: defaultCommand) + clOptions

    override fun preprocessCheckSatOutput(lines: Flow<String>) = flow<String> {
        // Buffer all lines; we might need to find a better way if this uses too much memory.
        val linesList = lines.toList()
        if (linesList.any { it.startsWith("[bitwuzla>main] ALARM TRIGGERED: time limit ") }) {
            /* pattern: [bitwuzla>main] ALARM TRIGGERED: time limit 10 seconds reached
             * - replace unknown with timeout
             * - drop other lines
             */
            if (linesList.all { it != "unknown" }) {
                logger.warn { "bitwuzla triggered time limit alarm, but did not respond unknown --> unexpected" }
            }
            emit("timeout")
        } else {
            emitAll(super.preprocessCheckSatOutput(linesList.asFlow()))
        }
    }

    private fun readResolve(): Any = BitwuzlaSolverInfo
}
