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
import utils.unused
import kotlin.time.Duration


/**
 * Represents the CVC5 (or CVC4) solver, and stores some metadata on it.
 *
 * Description of some CVC5 Flags:
 *  - `--lang` input language (we use `smt2`)
 *  - `--tlimit` process time limit (millis)
 *  - `--tlimit-per` per-query time limit
 *  - `--incremental`/`--no-incremental` incremental mode -- must be on for push/pop; solver can be faster when this is
 *     "off"
 *  - `--full-saturate-quant`: not totally clear, cvc4 sometimes gives up on quantifiers -- less so with this flag
 *  - `--nl-ext-tplanes`, `--decision=justification`: modify nonlinear solver -- most successful according to Andy
 */
object CVC5SolverInfo : SolverInfo(name = "CVC5") {

    override fun getOptionForIncremental(): List<String> = listOf("--incremental")
    override fun getOptionForTimelimit(timelimit: Duration): List<String> = listOf("--tlimit-per=${timelimit.inWholeMilliseconds}")

    override fun supportsLogicFeatures(features: SolverConfig.LogicFeatures): Boolean = true

    override val supportsNewSmtLibBvOverflowSymbols get() = true

    override fun getOptionForRandomSeed(randomSeed: Int): List<String> = listOf("--seed=$randomSeed")

    override fun getCmdToChangeTimelimit(timelimit: Duration) = "(set-option :tlimit-per ${timelimit.inWholeMilliseconds})"

    private const val DEFAULT_CVC_COMMAND = "cvc5"

    // --dag-thresh=0: temporary (verified) fix to ensure models produced by CVC5 do not contain "lets"
    // -q: to make sure cvc5 does not flood stderr with warnings (which we've had trouble with in the past)
    override fun commandForStdInMode(clOptions: List<String>, customBinary: String?): List<String> =
        listOf(customBinary ?: DEFAULT_CVC_COMMAND, "--lang", "smt2", "--dag-thresh=0", "-q") + clOptions

    override val defaultCommand: String
        get() = DEFAULT_CVC_COMMAND

    fun getQuantifierConfigs(timelimit: Duration, memlimitBytes: Long?, incrementalMode: Boolean): List<SolverConfig>{
        return listOf(SolverConfig.cvc5.q.copy(
            timelimit = timelimit,
            memlimitBytes = memlimitBytes,
            incremental = incrementalMode

        ))
    }

    fun getNonLinearConfigs(timelimit: Duration, memlimitBytes: Long?, incrementalMode: Boolean): List<SolverConfig>{
        return listOf(SolverConfig.cvc5.nonlin.copy(
            timelimit = timelimit,
            memlimitBytes = memlimitBytes,
            incremental = incrementalMode
        ))
    }

    fun getBitVectorConfigs(timelimit: Duration, memlimitBytes: Long?, incrementalMode: Boolean): List<SolverConfig>{
        unused(timelimit)
        unused(memlimitBytes)
        unused(incrementalMode)
        return listOf() //there seems to be a bug in BV mode, see above (CVC5)
    }

    private fun readResolve(): Any = CVC5SolverInfo
}


object CVC4SolverInfo : SolverInfo("CVC4") {
    override val defaultCommand: String
        get() = "cvc4"

    override fun getOptionForIncremental(): List<String> = listOf("--incremental")
    override fun getOptionForTimelimit(timelimit: Duration): List<String> = listOf("--tlimit-per=${timelimit.inWholeMilliseconds}")

    override fun supportsLogicFeatures(features: SolverConfig.LogicFeatures): Boolean = true

    override fun getOptionForRandomSeed(randomSeed: Int): List<String> = listOf("--seed=$randomSeed")

    override fun commandForStdInMode(clOptions: List<String>, customBinary: String?): List<String> =
        listOf(customBinary ?: defaultCommand, "--lang", "smt2") + clOptions

    fun getQuantifierConfigs(timelimit: Duration, memlimitBytes: Long?, incrementalMode: Boolean): List<SolverConfig>{
        return listOf(
                SolverConfig.cvc4.q.copy(
                    timelimit = timelimit,
                    memlimitBytes = memlimitBytes,
                    incremental = incrementalMode
                ))
    }

    fun getNonLinearConfigs(timelimit: Duration, memlimitBytes: Long?, incrementalMode: Boolean): List<SolverConfig>{
        return listOf(
            SolverConfig.cvc4.nonlin.copy(timelimit = timelimit, memlimitBytes = memlimitBytes, incremental = incrementalMode)
        )
    }

    fun getBitVectorConfigs(timelimit: Duration, memlimitBytes: Long?, incrementalMode: Boolean): List<SolverConfig>{
        unused(timelimit)
        unused(memlimitBytes)
        unused(incrementalMode)
        return listOf() //there seems to be a bug in BV mode, see above (CVC5)
    }

    private fun readResolve(): Any = CVC4SolverInfo
}
