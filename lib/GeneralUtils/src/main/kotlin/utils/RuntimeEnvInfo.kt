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

package utils

import solver.*
import java.io.IOException
import kotlin.time.Duration
import java.util.concurrent.TimeUnit
import datastructures.stdcollections.*

/**
 * Utilities that help with assessing the environment that the tool is running in.
 */
object RuntimeEnvInfo {

    private const val timeoutCommandDefaultTimeoutSeconds: Long = 600L

    private const val simpleCommandTimeoutSeconds = 3L

    /**
     * Executes the given command [cmd] in the current environment and returns the concatenation of what it printed to
     * stdout and to stderr .
     * The command [cmd] needs to be given as multiple strings for the command itself and its arguments instead of
     * a single commandline string, for example `getCommandOutput("z3", "--version")` instead of
     * `getCommandOutput("z3 --version")`.
     * The return value is `null` in any of the following cases:
     * - the command is not executable
     * - the command does not finish within [simpleCommandTimeoutSeconds] seconds
     * - the command terminates with nonzero exit code
     * - any other exception is thrown along the way
     *
     * @return a pair of strings, the first for `stdout`, the second for `stderr`, or null (e.g. if the process
     *      didn't start)
     */
    private fun getCommandOutput(vararg cmd: String): Pair<String,String>? {
        val proc = try {
            Runtime.getRuntime().exec(cmd)
        } catch (_: IOException) {
            return null
        }
        val procOutput = proc.inputStream.bufferedReader()
        val procError = proc.errorStream.bufferedReader()
        try {
            proc.waitFor(simpleCommandTimeoutSeconds, TimeUnit.SECONDS)
        } catch (e: InterruptedException) {
            return null
        }
        val output = mutableListOf<String>()
        val error = mutableListOf<String>()
        try {
            while (procOutput.ready() || procError.ready()) {
                if (procOutput.ready()) {
                    output.add(procOutput.readLine())
                }
                if (procError.ready()) {
                    error.add(procError.readLine())
                }
            }
        } catch (_: IOException) {
            return null
        }
        val exitVal = try {
            proc.exitValue()
        } catch (_: IllegalThreadStateException) {
            proc.destroyForcibly()
            return null
        }
        return if (exitVal == 0) {
            output.joinToString("\n") to error.joinToString("\n")
        } else {
            null
        }
    }

    private const val timeoutCommand = "timeout"

    /**
     * @return the output that the solver gives when asked for its version; null if the solver's default executable is
     *   unavailable
     */
    fun getSolverVersionIfAvailable(solver: SolverInfo, versionFlag: String = "--version"): Pair<String, String>? {
        return getCommandOutput(solver.defaultCommand, versionFlag)
    }

    val isTimeoutCommandAvailable by lazy { getCommandOutput(timeoutCommand, "--version") != null }

    /** will return an empty list if there is no timeout command available
     *
     * Notes:
     *  - takes the solver timeout as input, timeout command will fire three seconds after that
     * `-k` option sends an extra SIGKILL signal three seconds after timeout command first fires (sending a SIGTERM)
     * */
    @Suppress("unused")
    fun getTimeoutCommandIfAvailable(timeout: Duration?): List<String> =
        if (isTimeoutCommandAvailable) {
            listOf(timeoutCommand, "-k", "3s", "${(timeout?.inWholeSeconds ?: timeoutCommandDefaultTimeoutSeconds) + 3}")
        } else {
            listOf()
        }


    private const val prlimitCommand = "prlimit"


    val isPrlimitCommandAvailable by lazy { getCommandOutput(prlimitCommand, "--version") != null }

    /** will return an empty list if there is no `prlimit` command available */
    fun getPrlimitCommandIfAvailable(memLimitBytes: Long?): List<String> =
        if (memLimitBytes != null && isPrlimitCommandAvailable) {
            check(memLimitBytes >= 0)
            { "a negative value for memlimit will be ignored" }
            listOf(prlimitCommand, "--as=$memLimitBytes")
        } else {
            listOf()
        }


}
