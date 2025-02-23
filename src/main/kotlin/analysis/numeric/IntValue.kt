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

@file:kotlinx.serialization.UseSerializers(BigIntegerSerializer::class)
package analysis.numeric

import com.certora.collect.*
import evm.EVM_BITWIDTH256
import evm.MAX_EVM_UINT256
import utils.*
import java.math.BigInteger


val MAX_UINT = MAX_EVM_UINT256

val UINT_BITWIDTH = EVM_BITWIDTH256.toBigInteger()

/**
    Intervals over uint256.
    It is expected that [lb] and [ub] will not contain negative numbers, but this is **not** checked.
 */
@KSerializable
@Treapable
class IntValue(
    val lb: BigInteger,
    val ub: BigInteger
) :
    AmbiSerializable,
    UIntApprox<IntValue>,
    WithUIntApproximation<IntValue> {

    init {
        if (!(lb <= ub)) {
            throw IllegalStateException("Invalid interval: $lb, $ub")
        }
    }

    override fun getUpperBound(): BigInteger = ub

    override val x get() = this

    companion object {
        fun Constant(x: BigInteger) = IntValue(x, x)
        fun Interval(lb: BigInteger? = null, ub: BigInteger? = null): IntValue = IntValue(lb ?: BigInteger.ZERO, ub ?: MAX_UINT)

        val Nondet = IntValue(BigInteger.ZERO, MAX_UINT)
    }

    override fun mult(other: IntValue): Pair<IntValue, Boolean> {
        val newUb = this.ub * other.ub
        return if (newUb > MAX_UINT) {
            Nondet to true
        } else {
            IntValue(ub = newUb,
                    lb = other.lb * this.lb
            ) to false
        }
    }

    override fun add(other: IntValue) : Pair<IntValue, Boolean> {
        val newUb = this.ub + other.ub
        return if(newUb > MAX_UINT) {
            Nondet to true
        } else {
            IntValue(
                    ub = newUb,
                    lb = other.lb + this.lb
            ) to false
        }
    }

    fun isDefinitelyGreaterThan(lowerBound: BigInteger): Boolean {
        return this.lb > lowerBound
    }
    override fun shiftLeft(lb: BigInteger, ub: BigInteger): IntValue {
        if(overflowsBitwidth(ub, this.ub)) {
            return Nondet
        }
        assert(!overflowsBitwidth(lb, this.ub)) {
            "The lower bound on the shift $lb overflows ${this.ub} by $ub did not?"
        }
        val newUb = this.ub.shiftLeft(ub.toInt())
        assert(!overflowsBitwidth(lb, this.lb)) {
            "The lower bound on the shift $lb overflows ${this.lb}, but the upper bound ${this.ub} and $ub do not?"
        }
        val newLb = this.lb.shiftLeft(lb.toInt())
        return IntValue(lb = newLb, ub = newUb)
    }

    private fun overflowsBitwidth(shiftBy: BigInteger, target: BigInteger): Boolean =
        shiftBy > (UINT_BITWIDTH.toInt() - target.bitLength()).toBigInteger()

    fun shiftLeft(lb: BigInteger): IntValue {
        return if(lb >= UINT_BITWIDTH) {
            Constant(BigInteger.ZERO)
        } else if(this.isDefinitelyGreaterThan(BigInteger.ZERO)) {
            IntValue(lb = BigInteger.TWO.pow(lb.toInt()), ub = MAX_UINT)
        } else {
            Nondet
        }
    }

    override fun sub(other: IntValue): Pair<IntValue, Boolean> {
        val newLb = this.lb - other.ub
        val newUb = this.ub - other.lb
        return if(newLb < BigInteger.ZERO) {
            Nondet to true
        } else {
            IntValue(lb = newLb, ub = newUb) to false
        }
    }

    fun mayNotEqual(v: BigInteger) : Boolean = !this.mustEqual(v)

    @Suppress("unused")
    fun mayIntersect(v: IntValue) : Boolean =
            !(this.getUpperBound() < v.getLowerBound() || this.getLowerBound() > v.getUpperBound())

    override fun getLowerBound(): BigInteger = this.lb

    /**
     * Like [withLowerBound] intersect this interval with the closed
     * interval from zero up to [newUb]. If the intersection is empty, we have
     * a contradiction but this implementation ignores it
     */
    fun withUpperBound(newUb: BigInteger) : IntValue {
        return if(newUb < this.ub && newUb >= this.lb) {
            this.copy(ub = newUb)
        } else {
            this
        }
    }
    /**
       Intersect this interval with the closed interval beginning at [newLb]
       and extending to [MAX_UINT]. Technically, if the intersection is empty
       we have a contradiction, but this implementation happily ignores that.
     */
    fun withLowerBound(newLb: BigInteger): IntValue {
        return if(newLb > this.lb && newLb <= this.ub) {
            this.copy(lb = newLb)
        } else {
            this
        }
    }
    override fun join(other: IntValue): IntValue {
        if(this === other) {
            return other
        }
        return this.copy(
                lb = this.lb.min(other.lb),
                ub = this.ub.max(other.ub)
        )
    }

    override fun widen(next: IntValue): IntValue {
        if(this === next) {
            return this
        }
        return this.copy(
                lb = if(next.lb < this.lb) { BigInteger.ZERO } else this.lb,
                ub = if(next.ub > this.ub) { MAX_UINT } else this.ub
        )
    }

    override val c : BigInteger
        get() {
            if(!this.isConstant) {
                throw UnsupportedOperationException("Interval $this is not a constant")
            }
            return this.lb
        }

    override fun shiftRight(lb: BigInteger, ub: BigInteger): IntValue {
        if(!lb.isInt()) {
            return Constant(BigInteger.ZERO)
        }
        if(!ub.isInt()) {
            return Nondet
        }
        val newUb = this.ub.shiftRight(lb.intValueExact())
        val newLb = this.lb.shiftRight(ub.intValueExact())
        return IntValue(newLb, newUb)
    }

    override val isConstant : Boolean get() = this.lb == this.ub

    override fun mayOverlap(other: IntValue): Boolean {
        return !this.mustNotOverlap(other)
    }

    fun mustNotOverlap(other: IntValue): Boolean {
        return this.lb > other.ub || this.ub < other.lb
    }

    fun updateBounds(lb: BigInteger?, ub: BigInteger?): IntValue {
        val newLb = if(lb != null && lb > this.lb) {
            lb
        } else {
            this.lb
        }
        val newUb = if(ub != null && ub < this.ub) {
            ub
        } else {
            this.ub
        }
        return if(newLb <= newUb) {
            Interval(newLb, newUb)
        } else {
            this
        }
    }

    fun copy(lb: BigInteger? = this.lb, ub: BigInteger? = this.ub) : IntValue = Interval(lb, ub)



    override fun equals(other: Any?): Boolean {
        if (this === other) return true
        if (other !is IntValue) return false

        if (lb != other.lb) return false
        if (ub != other.ub) return false

        return true
    }

    override fun hashCode(): Int {
        var result = lb.hashCode()
        result = 31 * result + ub.hashCode()
        return result
    }

    override fun toString(): String {
        return "IntValue(lb=$lb, ub=$ub)"
    }


}
