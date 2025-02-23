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

package analysis.numeric.linear

import java.math.BigInteger

/**
 * A rational number composed of a numerator [num] and denominator [denom]
 */
data class Rational(
        val num: BigInteger,
        val denom: BigInteger
) {
    init {
        assert(denom != BigInteger.ZERO)
    }

    private lateinit var canon : Rational

    /**
     * Canonicalizes the representation of this rational number. In the following, `[[r]]` denotes the mathematical
     * interpretation of this rational number.
     * A canonicalized rational number fulfills the following criteria:*
     * 1) if [[r]] == 0, then [num] == 0 and [denom] == 1
     * 2) If [[r]] in Z, then [denom] == 1
     * 3) If [[r]] >= 0, then [num] >= 0 and [denom] > 0
     * 4) [denom] > 0
     * 5) gcd([num], [denom]) == 1
     *
     * The result of this function is cached.
     */
    fun canonicalize() : Rational {
        /*
          Enforce condition 1
         */
        if(num == BigInteger.ZERO) {
            return ZERO
        }
        /*
          Short circuit, 2 - 5 are trivially satisfied
         */
        if(denom == BigInteger.ONE) {
            return this
        }
        if(this::canon.isInitialized) {
            return canon
        }
        var n = this.num
        var d = this.denom
        /* Enforce 3-4 */
        if(d < BigInteger.ZERO) {
            n = n.negate()
            d = d.negate()
        }
        assert(d > BigInteger.ZERO)
        /* Check condition 5 */
        if(d == BigInteger.ONE) {
            canon = Rational(num = n, denom = d)
            return canon
        }
        val gcd = n.gcd(d)
        /* Condition 5 */
        if(gcd != BigInteger.ONE) {
            n /= gcd
            d /= gcd
        }
        /* Cache */
        canon = Rational(num = n, denom = d)
        return canon
    }

    /**
      Check if the absolute value of this rational number is not equal to 1
     */
    fun absNotOne() : Boolean = this.canonicalize() != ONE && this.canonicalize() != NEG_ONE /* canonicalization is cached */

    companion object {
        /**
         * For any n, give 1/n
         */
        fun inv(denom: BigInteger) = Rational(
                BigInteger.ONE, denom)

        val ONE = Rational(BigInteger.ONE,
                BigInteger.ONE)

        val NEG_ONE = Rational(
                BigInteger.ONE.negate(), BigInteger.ONE)

        val ZERO = Rational(BigInteger.ZERO,
                BigInteger.ONE)

        /**
         * For any n, give the rational representation, i.e. n / 1
         */
        fun nat(num: BigInteger) = Rational(num,
                BigInteger.ONE)

        val `1` = ONE
        val `0` = ZERO
        val `-1` = NEG_ONE
    }


    /**
      For a rational value r, give 1/r (not total, will fail with [[r]] == 0)
     */
    fun invert() : Rational = Rational(
            denom, num)

    infix operator fun plus(other: Rational) =
        Rational(
                (num * other.denom) + (other.num * this.denom),
                this.denom * other.denom
        ).canonicalize()

    infix operator fun minus(other: Rational) =
            Rational(
                    (num * other.denom) - (other.num * this.denom),
                    this.denom * other.denom
            ).canonicalize()

    infix operator fun times(other: Rational) =
            Rational(
                    num * other.num,
                    this.denom * other.denom
            ).canonicalize()

    infix operator fun times(other: BigInteger) = Rational(
            num * other,
            denom = this.denom
    ).canonicalize()

    fun neg(): Rational {
        return this.copy(num = num.negate())
    }

    infix operator fun div(other: BigInteger) = Rational(
            num,
            denom = this.denom * other
    ).canonicalize()

    infix operator fun rem(other: BigInteger) : Rational =
            Rational(num % (other * this.denom),
                this.denom).canonicalize()

    operator fun unaryMinus() = this.neg()

    fun isNegative(): Boolean =
        (num < BigInteger.ZERO && denom > BigInteger.ZERO) ||
                (num > BigInteger.ZERO && denom < BigInteger.ZERO)
}