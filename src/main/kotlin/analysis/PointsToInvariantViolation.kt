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

package analysis

import java.lang.Exception
import kotlin.contracts.ExperimentalContracts
import kotlin.contracts.contract

class PointsToInvariantViolation(msg: String, t: Throwable? = null) : Exception(msg, t)

@OptIn(ExperimentalContracts::class)
inline fun ptaInvariant(b: Boolean, f: () -> String) {
    contract {
        returns() implies b
    }
    if (!b) {
        throw PointsToInvariantViolation(f())
    }
}
