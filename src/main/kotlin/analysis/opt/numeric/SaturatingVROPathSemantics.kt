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

import analysis.LTACCmd
import analysis.numeric.BoundedQIntPropagationSemantics
import analysis.numeric.QualifierPropagationComputation
import analysis.opt.intervals.ExtBig.Companion.asExtBig
import analysis.opt.intervals.ExtBig.Companion.max
import analysis.opt.intervals.ExtBig.Companion.min
import com.certora.collect.*
import vc.data.TACSummary
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * A basic implementation of [BoundedQIntPropagationSemantics] which uses the [VROQualifierPropagation] but also aggressively
 * incorporates information from must equals. In other words, when propagating the fact that `x == y` (as a new [analysis.opt.numeric.VROQuals.MustEqual]
 * qualifier on x), this will aggressively find the bounds on `y` and it's qualifiers and propgate that onto `x`.
 */
abstract class SaturatingVROPathSemantics<S: Map<TACSymbol.Var, VROInt>>(
    propagator: QualifierPropagationComputation<VROInt, S, Any, VROQuals> = VROQualifierPropagation()
) : BoundedQIntPropagationSemantics<VROInt, VROQuals, S,  Any>(propagator = propagator) {
    override fun applyPath(
        k: TACSymbol.Var,
        curr: VROInt,
        lb: BigInteger?,
        ub: BigInteger?,
        quals: Iterable<VROQuals>,
        st: S,
        l: LTACCmd
    ) : S {
        val st_ = super.applyPath(k, curr, lb, ub, quals, st, l)
        var stateIter = st_
        for(q in curr.qual) {
            if(q !is VROQuals.MustEqual) {
                continue
            }
            val saturated = st_.interp(q.other)
            val updated = saturated.withBoundAndQualifiers(
                lb = lb?.asExtBig?.max(saturated.lb) ?: saturated.lb,
                ub = ub?.asExtBig?.min(saturated.ub) ?: saturated.ub,
                quals = saturated.qual + quals
            )
            stateIter = assignVar(stateIter, q.other, updated, l)
        }
        return stateIter
    }

    override fun propagateSummary(
        summary: TACSummary,
        s: S,
        w: Any,
        l: LTACCmd
    ): S {
        return s
    }
}
