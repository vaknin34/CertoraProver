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

object PathApplication {
    data class PropagatedInformation<Q>(
        val lb: BigInteger?,
        val ub: BigInteger?,
        val q: Iterable<Q>
    )

    /**
     * From the path information [p] propagated to the value [curr], compute the [PropagatedInformation]
     * that holds the induced upper and lower bounds along with any new qualifiers.
     *
     * `adapter` lifts the [IntQualifier] into the domain of qualifiers [Q]. [handlePath] may be
     * used to propagate additional qualifiers based on path information found in [p]
     */
    fun <I, Q> computePathInfo(
        curr : I,
        p: List<PathInformation<Q>>,
        handlePath: (PathInformation<Q>, I, MutableList<Q>) -> Unit
    ): PropagatedInformation<Q> {
        var lb : BigInteger? = null
        var ub : BigInteger? = null
        val selfQuals = mutableListOf<Q>()
        val quals = mutableListOf<Q>()
        for(pi in p) {
            handlePath(pi, curr, selfQuals)
            when(pi) {
                is PathInformation.StrictUpperBound -> {
                    if(pi.num != null) {
                        ub = ub?.min(pi.num - BigInteger.ONE) ?: (pi.num - BigInteger.ONE)
                    }
                }
                is PathInformation.StrictLowerBound -> {
                    if(pi.num != null) {
                        lb = lb?.max(pi.num + BigInteger.ONE) ?: (pi.num + BigInteger.ONE)
                    }
                }
                is PathInformation.WeakLowerBound -> {
                    if(pi.num != null) {
                        lb = lb?.max(pi.num) ?: pi.num
                    }
                }
                is PathInformation.WeakUpperBound -> {
                    if(pi.num != null) {
                        ub = ub?.min(pi.num) ?: pi.num
                    }
                }
                is PathInformation.Qual -> {
                    quals.add(pi.q)
                }
                is PathInformation.StrictEquality -> {
                    if(pi.num != null) {
                        lb = pi.num
                        ub = pi.num
                    }
                }
                /* on behalf of jtoman:
                it is always sound to ignore bounds.
                iirc, it's difficult to express signed bounds because our model is in terms of a single closed interval,
                whereas propagating that something is signed less than another value requires us to
                express two disjoint intervals.
                thus ignoring here the other cases for signed is intentional
                 */
                else -> {}
            }
        }
        return PropagatedInformation(
                lb = lb,
                ub = ub,
                q = selfQuals + quals
        )
    }

    /**
     * A simpler version of [computePathInfo], which uses [IntQualifier] for the qualifier domain
     * and provides no additional qualifiers.
     */
    fun <T> computeSimplePathInfo(p: List<PathInformation<T>>): PropagatedInformation<T> {
        return computePathInfo(null, p) { _, _, _ ->

        }
    }
}