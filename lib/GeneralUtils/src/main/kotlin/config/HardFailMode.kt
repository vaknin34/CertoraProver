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

package config

/**
 * Used to describe what is the expected behaviour in a case of a failure in CVT.
 * Currently used for CallTrace construction and unapplied summaries failures.
 *
 * 1. For CallTrace:
 * Describes the behavior when an error occurs while building the Call Trace
 * and consequently the Call Trace is unavailable.
 * In addition, enabling this setting leads to a stricter policy for enforcing that the
 * call stack is not malformed - the call trace will not attempt to recover in case of unexpected
 * call stack.
 *
 * 2. For unapplied summaries:
 * Describes the behaviour when unapplied summaries are detected.
 *
 * This setting may allow such exceptions to also terminate the execution of CVT (by re-throwing it).
 * This feature could be used to signal automated tests that such failures occurred.
 *
 * [OFF] The error will be caught and logged, and CVT execution will continue.
 * [ON] The error will not be caught, which will immediately stop CVT execution.
 */
enum class HardFailMode(val configString: String, val desc: String) {
    OFF(configString = "off", desc = "if error is caught, continue execution"),
    ON(configString = "on", desc = "if error is caught, stop execution"),
    ;

    companion object {
        fun paramDescriptions() = buildString {
            values().forEach { appendLine("${it.configString} - ${it.desc}") }
        }
    }
}
