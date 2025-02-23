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

import evm.MAX_EVM_UINT256
import java.math.BigInteger

val maxUint = MAX_EVM_UINT256

sealed class ConstSet : UIntApprox<ConstSet> {
    companion object {
        fun Constant(v: BigInteger) = C(setOf(v))
    }

    object Nondet : ConstSet() {
        override fun getUpperBound(): BigInteger {
            return maxUint
        }

        override fun getLowerBound(): BigInteger {
            return BigInteger.ZERO
        }

        override fun mult(other: ConstSet): Pair<ConstSet, Boolean> {
            return this to true
        }

        override fun add(other: ConstSet): Pair<ConstSet, Boolean> {
            return this to true
        }

        override fun sub(other: ConstSet): Pair<ConstSet, Boolean> {
            return this to true
        }

        override fun shiftLeft(lb: BigInteger, ub: BigInteger): ConstSet {
            return this
        }

        override fun mayOverlap(other: ConstSet): Boolean {
            return true
        }

        override val isConstant: Boolean
            get() = false
        override val c: BigInteger
            get() = error("Not a constant")

        override fun shiftRight(lb: BigInteger, ub: BigInteger): ConstSet {
            return this
        }

        override fun widen(next: ConstSet): ConstSet {
            return this
        }

        override fun join(other: ConstSet): ConstSet {
            return this
        }
    }

    data class C(val ks: Set<BigInteger>) : ConstSet() {
        init {
            assert(ks.isNotEmpty())
        }

        override fun getUpperBound(): BigInteger {
            return ks.maxOrNull()!!
        }

        override fun getLowerBound(): BigInteger {
            return ks.minOrNull()!!
        }

        override fun mult(other: ConstSet): Pair<ConstSet, Boolean> {
            if(other == Nondet) {
                return other to true
            }
            return this.binOp(other as C, BigInteger::multiply)
        }

        override fun add(other: ConstSet): Pair<ConstSet, Boolean> {
            if(other !is C) {
                return Nondet to true
            }
            return this.binOp(other, BigInteger::add)
        }

        override fun sub(other: ConstSet): Pair<ConstSet, Boolean> {
            if(other !is C) {
                return Nondet to true
            }
            return this.binOp(other, BigInteger::subtract)
        }

        override fun shiftLeft(lb: BigInteger, ub: BigInteger): ConstSet {
            if(lb == ub && lb < 256.toBigInteger()) {
                val res = mutableSetOf<BigInteger>()
                this.ks.mapTo(res) { x ->
                    x.shiftLeft(lb.toInt()) and maxUint
                }
                return C(res)
            }
            return Nondet
        }

        override fun mayOverlap(other: ConstSet): Boolean {
            if(other !is C) {
                return true
            }
            return other.ks.intersect(this.ks).isNotEmpty()
        }

        private fun binOp(other: C, sem: (BigInteger, BigInteger) -> BigInteger) : Pair<ConstSet, Boolean> =
            this.ks.flatMap { o1 ->
                other.ks.map { o2 ->
                    val res = sem(o1, o2)
                    if(res > maxUint || res < BigInteger.ZERO) {
                        return Nondet to true
                    }
                    res
                }
            }.toSet().let(ConstSet::C) to false

        override val isConstant: Boolean
            get() = ks.size == 1
        override val c: BigInteger
            get() = ks.first()

        override fun shiftRight(lb: BigInteger, ub: BigInteger): ConstSet {
            return if(lb == ub && lb < UINT_BITWIDTH) {
                ks.mapTo(mutableSetOf()) {
                    it.shiftLeft(lb.toInt())
                }.let(::C)
            } else {
                Nondet
            }
        }

        override fun widen(next: ConstSet): ConstSet {
            if(next !is C) {
                return Nondet
            }
            if(!this.ks.containsAll(next.ks)) {
                return Nondet
            }
            return this
        }

        override fun join(other: ConstSet): ConstSet {
            if(other !is C) {
                return Nondet
            }
            return C(this.ks.union(other.ks))
        }
    }
}