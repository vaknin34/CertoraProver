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

package analysis.pta.abi

import analysis.pta.PointsToDomain
import analysis.pta.abi.EncoderAnalysis.EncodingState.Companion.variablesEqualTo
import evm.EVM_WORD_SIZE
import log.Logger
import log.LoggerTypes
import utils.`impossible!`
import vc.data.TACSymbol
import java.math.BigInteger

interface StridingQualifier {
    val stridePath: StridePath
    val strideBy: BigInteger
    val innerOffset: BigInteger

    fun toFullPath(): StridePath = this.stridePath.appendLoop(this.strideBy).appendConstStep(innerOffset)

    companion object {
        private val logger = Logger(LoggerTypes.ABI_ENCODER)

        fun <T : StridingQualifier> joinMismatchedField(
                k1: BigInteger,
                s1: PointsToDomain,
                k2: BigInteger,
                s2: PointsToDomain,
                f: (StridePath, BigInteger, Set<TACSymbol.Var>) -> T
        ) : T? {
            return if((k1 - k2).abs().mod(EVM_WORD_SIZE) == BigInteger.ZERO) {
                val ind = if(k1 > k2) {
                    s2.variablesEqualTo(BigInteger.ZERO).intersect(s1.variablesEqualTo(BigInteger.ONE))
                } else {
                    s1.variablesEqualTo(BigInteger.ZERO).intersect(s2.variablesEqualTo(BigInteger.ONE))
                }
                f(
                    StridePath(
                            root = k1.min(k2),
                            path = listOf()
                    ),
                    (k1 - k2).abs(),
                    ind
                )
            } else {
                null
            }
        }

        fun <T: StridingQualifier> joinStridePaths(left: T, right: T, f: (T, StridePath) -> T) : T? {
            if(left.strideBy == right.strideBy && right.stridePath == left.stridePath && left.innerOffset == right.innerOffset) {
                return left
            }
            if(left.innerOffset != BigInteger.ZERO && right.innerOffset != BigInteger.ZERO) {
                logger.info {
                    "Have incompatible inner offsets, refusing to handle this"
                }
                return null
            }
            if(right.strideBy == left.strideBy) {
                if(right.innerOffset != left.innerOffset) {
                    return null
                } else if(left.stridePath.path.size <= right.stridePath.path.size && left.stridePath.path.withIndex().all {
                            right.stridePath.path[it.index] == it.value
                        }) {
                    return right
                } else if(right.stridePath.path.size <= left.stridePath.path.size && right.stridePath.path.withIndex().all {
                            left.stridePath.path[it.index] == it.value
                        }) {
                    return left
                } else {
                    return null
                }
            } else if(right.strideBy < left.strideBy) {
                if(right.innerOffset != BigInteger.ZERO || !isConsistent(p1 = left.toFullPath(), p2 = right.stridePath)) {
                    return null
                }
                return f(right, left.toFullPath())
            } else if(left.strideBy < right.strideBy) {
                if(left.innerOffset != BigInteger.ZERO || !isConsistent(p1 = right.toFullPath(), p2 = left.stridePath)) {
                    return null
                }
                return f(left, right.toFullPath())
            } else {
                `impossible!`
            }
        }

        // stride path "solver"
        private tailrec fun isConsistent(p1: StridePath, p2: StridePath) : Boolean {
            if(p1.path.isNotEmpty() && p2.path.isNotEmpty()) {
                if(p1.path.last() != p2.path.last()) {
                    return false
                }
                return isConsistent(p1.copy(path = p1.path.dropLast(1)), p2.copy(path = p2.path.dropLast(1)))
            } else if(p1.path.isNotEmpty() && p2.path.isEmpty()) {
                return checkRootConsistency(p1, p2.root)
            } else if(p2.path.isNotEmpty() && p1.path.isEmpty()) {
                return checkRootConsistency(p2, p1.root)
            } else return p1.path.isEmpty() && p2.path.isEmpty() && p1.root == p2.root
        }

        private fun checkRootConsistency(p1: StridePath, root: BigInteger): Boolean {
            if (p1.root > root) {
                return false
            }
            val tgt = p1.path.fold(root) { Curr, p ->
                if (p is StrideStep.ConstStep) {
                    Curr - p.c
                } else {
                    Curr
                }
            } - p1.root
            if (tgt < BigInteger.ZERO) {
                return false
            }
            if (tgt == BigInteger.ZERO) {
                return true
            }
            val coefficients = p1.path.filterIsInstance<StrideStep.StrideLoop>().map {
                it.c
            }.filter {
                it != BigInteger.ZERO
            }
            if (coefficients.isEmpty()) {
                return false
            }
            return solveDiophantine(coefficients, 0, tgt)
        }

        private fun solveDiophantine(coefficients: List<BigInteger>, i: Int, tgt: BigInteger) : Boolean {
            val c = coefficients[i]
            if(tgt.mod(c) == BigInteger.ZERO) {
                return true
            }
            if(i == coefficients.lastIndex) {
                return false
            }
            var it = BigInteger.ZERO
            while(it < tgt / c) {
                check((tgt - it * c) >= BigInteger.ZERO) {
                    "Math is broken, have that $it is < $tgt / $c but ($tgt - $it * $c) is negative?"
                }
                if(solveDiophantine(coefficients, i + 1, tgt - (it * c))) {
                    return true
                }
                it += BigInteger.ONE
            }
            return false
       }

        fun <T : StridingQualifier, R : FieldPointer> joinStridingAndField(left: T, right: R): T? {
            if (left.innerOffset > right.offset) {
                return null
            }
            if (!checkRootConsistency(left.stridePath.appendLoop(left.strideBy), right.offset - left.innerOffset)) {
                return null
            }
            return left
        }

    }
}
