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
import utils.RuntimeEnvInfo
import kotlin.time.Duration


object SmtInterpolSolverInfo : SolverInfo(name = "SmtInterpol") {
    private val alwaysOnOptions = listOf(
        // same memory config as for CertoraProver -- as suggested by Eric
        "-Xmx31g",
        "-XX:MaxHeapFreeRatio=10",
        "-XX:MinHeapFreeRatio=5",
        "-XX:G1PeriodicGCInterval=15",
        // " -q",  smtinterpol.sh has this option built in already
    )

    private const val DEFAULT_SMTINTERPOL_COMMAND = "smtinterpol.sh"

    override val versionQuery: String
        get() = "-version"

    override fun getOptionForTimelimit(timelimit: Duration): List<String> =
        listOf("-t", "${timelimit.inWholeMilliseconds}")

    override fun getOptionForRandomSeed(randomSeed: Int): List<String> =
        listOf("-r", "$randomSeed")

    override fun supportsLogicFeatures(features: SolverConfig.LogicFeatures): Boolean =
        features.arithmeticOperations != ArithmeticOperations.NonLinear &&
            features.arithmeticOperations != ArithmeticOperations.BitVector

    override fun getSolverVersionStringOrNull(): String? =
        RuntimeEnvInfo.getSolverVersionIfAvailable(this, versionQuery)?.second?.lines()?.get(0)

    /**
    *  `smtinterpol.sh` collects all leading options starting with `-X` and puts them before the `-jar`, so they're
    *  java options; the rest, by convention, are options for SMTInterpol itself.
     * This is used to set the max heap size for smtinterpol's JVM instance.
    */
    private fun checkOptionsOrder(options: List<String>): List<String> {
        var sawNonX = false
        options.forEach { option ->
            @Suppress("ForbiddenMethodCall") // a check involving options parsing -- needs a little string ops
            if (option.startsWith("-X")) {
                check(!sawNonX) { "giving an option starting with '-X' to smtinterpol.sh after giving one that does " +
                    "not start with -X --> looks like an error in ordering the options. smtinterpol.sh expects java" +
                    "options starting with -X before all others." }
            } else {
                sawNonX = true
            }
        }
        return options
    }


    override fun commandForStdInMode(clOptions: List<String>, customBinary: String?): List<String> =
        listOf(customBinary ?: DEFAULT_SMTINTERPOL_COMMAND) +
            checkOptionsOrder(alwaysOnOptions + clOptions)

    override val defaultCommand: String
        get() = DEFAULT_SMTINTERPOL_COMMAND

    private fun readResolve(): Any = SmtInterpolSolverInfo
}
