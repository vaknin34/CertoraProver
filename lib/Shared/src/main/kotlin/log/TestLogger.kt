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

package log

/** "Quasi loggers" (tm) through which tests can easily observe internal behavior. In particular this allows for
 * structured data to be observed, not just strings. All `var`s here must be null during production run time. */
object TestLoggers {
    object CallTrace {
        /** Can be used to check that the "unknown value" that appears as an "X" in the call traces is never used during
         * some run. */
        var noXs: NoXs? = null
        /** No "X"s (unknown values) have been used in call trace model values. Also see [noXs] */
        class NoXs(var foundX: Boolean = false)
    }
}
