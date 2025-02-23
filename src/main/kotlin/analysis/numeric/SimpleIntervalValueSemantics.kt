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

package analysis.numeric

import java.math.BigInteger

/**
 * A value semantics that operate over [IntValue] and which are agnostic to any states.
 */
object SimpleIntervalValueSemantics : StatelessUIntValueSemantics<IntValue, IntValue>() {
    override fun lift(lb: BigInteger, ub: BigInteger): IntValue = IntValue.Interval(lb, ub)

    override fun lift(iVal: IntValue): IntValue = iVal

    override val nondet: IntValue
        get() = IntValue.Nondet
}