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

package analysis.opt.numeric

import analysis.numeric.BoundedQualifiedInt
import analysis.numeric.OpenInterval
import analysis.numeric.WithIntApproximation
import analysis.opt.intervals.ExtBig
import analysis.opt.intervals.ExtBig.Companion.asExtBig
import analysis.opt.intervals.Interval
import com.certora.collect.*
import tac.Tag
import java.math.BigInteger

/**
 * Basic abstraction for straight line, simple qualified int semantics.
 */
data class VROInt(override val x: OpenInterval, override val qual: TreapSet<VROQuals>) :
    BoundedQualifiedInt<VROInt, VROQuals, OpenInterval>, WithIntApproximation<OpenInterval> {
    override fun withQualifiers(x: Iterable<VROQuals>): VROInt = this.copy(qual = x.toTreapSet())

    fun addQualifier(newQual: VROQuals): VROInt = this.copy(qual = qual + newQual)

    fun addQualifiers(newQuals: Iterable<VROQuals>): VROInt = this.copy(qual = qual + newQuals)

    fun withBoundAndQualifiers(lb: ExtBig, ub: ExtBig, quals: Iterable<VROQuals>) : VROInt {
        val newInterval = Interval(lb, ub) intersect x.interval
        val i = if(newInterval is Interval.NonEmpty) {
            OpenInterval(newInterval)
        } else {
            x
        }
        return this.copy(
            x = i,
            qual = quals.toTreapSet()
        )
    }

    override fun withBoundAndQualifiers(lb: BigInteger, ub: BigInteger, quals: Iterable<VROQuals>): VROInt {
        return withBoundAndQualifiers(lb.asExtBig, ub.asExtBig, quals)
    }

    fun join(other: VROInt) : VROInt {
        if(this === other) {
            return this
        }
        if(this.x == other.x && this.qual === other.qual) {
            return this
        }
        if(this == other) {
            return this
        }
        val newX = if(this.x == other.x) {
            x
        } else {
            x.join(other.x)
        }
        val newQual = if(this.qual === other.qual || this.qual == other.qual) {
            this.qual
        } else {
            qual.intersect(other.qual)
        }
        return VROInt(newX, newQual)
    }

    companion object {
        fun Tag.nondetOf() = when(this) {
            Tag.Bit256 -> nondet256
            Tag.Bool -> nondetBool
            else -> nondetFull
        }

        val nondetFull = VROInt(OpenInterval(Interval.IFull), treapSetOf())
        val nondet256 = VROInt(OpenInterval(Interval.IFull256), treapSetOf())
        val nondetBool = VROInt(OpenInterval(Interval.IFullBool), treapSetOf())
    }

    val lb : ExtBig get() = x.interval.low
    val ub : ExtBig get() = x.interval.high
}
