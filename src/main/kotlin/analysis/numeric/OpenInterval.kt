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

import analysis.opt.intervals.ExtBig
import analysis.opt.intervals.ExtBig.Companion.asExtBig
import analysis.opt.intervals.Interval
import com.certora.collect.*
import java.math.BigInteger

@Treapable
@JvmInline
value class OpenInterval(
    val interval: Interval.NonEmpty
) : IntApprox<OpenInterval>, WithIntApproximation<OpenInterval> {
    constructor(v: Interval) : this(v as Interval.NonEmpty)
    constructor(lb: BigInteger, ub: BigInteger) : this(lb.asExtBig, ub.asExtBig)
    constructor(lb: ExtBig, ub: ExtBig) : this(Interval(lb, ub))
    constructor(c: BigInteger) : this(Interval(c))

    override fun getUpperBound(): BigInteger? {
        return interval.high.nOrNull()
    }

    override fun getLowerBound(): BigInteger? {
        return interval.low.nOrNull()
    }

    fun withUpperBound(other: BigInteger): OpenInterval {
        if(other in interval) {
            return OpenInterval(interval.low, other.asExtBig)
        } else {
            return this
        }
    }

    fun withLowerBound(other: BigInteger) : OpenInterval {
        if(other in interval) {
            return OpenInterval(other.asExtBig, interval.high)
        } else {
            return this
        }
    }


    private fun asUnsignedInterval(): IntValue? {
        return interval.takeIf { it containedIn Interval.IFull256 }?.let {
            IntValue.Interval(it.low.n, it.high.n)
        }
    }

    private fun IntValue.toOpen() = OpenInterval(
        Interval.NonEmpty(
            this.lb.asExtBig,
            this.ub.asExtBig
        )
    )

    override fun shiftLeft(lb: BigInteger, ub: BigInteger): OpenInterval {
        return this.asUnsignedInterval()?.shiftLeft(lb, ub)?.toOpen() ?: OpenInterval(Interval.IFull)
    }

    override val isConstant: Boolean
        get() = interval.isConst
    override val c: BigInteger
        get() = interval.asConst

    override fun shiftRight(lb: BigInteger, ub: BigInteger): OpenInterval {
        return this.asUnsignedInterval()?.shiftRight(lb, ub)?.toOpen() ?: OpenInterval(Interval.IFull)
    }

    override fun join(other: OpenInterval): OpenInterval {
        return OpenInterval((interval union other.interval).toSingle())
    }

    override fun widen(next: OpenInterval): OpenInterval {
        val nxtMin = if(next.interval.low < this.interval.low) {
            ExtBig.MInf
        } else {
            this.interval.low
        }
        val nxtMax = if(this.interval.high < next.interval.high) {
            ExtBig.Inf
        } else {
            this.interval.high
        }
        return OpenInterval(nxtMin, nxtMax)
    }


    override fun mayOverlap(other: OpenInterval): Boolean {
        return this.interval.intersect(other.interval) !is Interval.Empty
    }

    override fun sub(other: OpenInterval): Pair<OpenInterval, Boolean> {
        return OpenInterval(this.interval - other.interval) to false
    }

    override fun add(other: OpenInterval): Pair<OpenInterval, Boolean> {
        return OpenInterval(this.interval + other.interval) to false
    }

    override fun mult(other: OpenInterval): Pair<OpenInterval, Boolean> {
        return OpenInterval(this.interval * other.interval) to false
    }

    override val x: OpenInterval
        get() = this
}
