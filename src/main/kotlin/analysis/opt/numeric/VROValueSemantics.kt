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

import analysis.LTACCmdView
import analysis.numeric.*
import com.certora.collect.*
import config.Config
import utils.*
import vc.data.TACCmd
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * Basic VRO semantics for qualified intervals, with tracking of masking, symbolic must equals, and path conditions.
 *
 * Includes logic to statically determine the value `x == y` based on present must/must-not equals information.
 */
val VROBaseValueSemantics = object : DelegatingSemantics<Map<TACSymbol.Var, VROInt>, VROInt, Any>(
    object : IntValueSemantics<VROInt, OpenInterval, Any, Any>() {
        override fun lift(lb: BigInteger, ub: BigInteger): OpenInterval = OpenInterval(lb, ub)

        override fun lift(iVal: OpenInterval): VROInt = VROInt(iVal, treapSetOf())

        override val nondet: VROInt = VROInt.nondetFull
    }.withPathConditions(
        condition = VROQuals::Condition,
        conjunction = VROQuals::LogicalConnective,
        flip = {
            (it as? Flippable)?.flip()
        },
    ).withBasicMath(
        multipleOf = { null },
        maskedOf = VROQuals::MaskedOf,
    ),
) {
    override fun evalVar(
        interp: VROInt,
        s: TACSymbol.Var,
        toStep: Map<TACSymbol.Var, VROInt>,
        input: Map<TACSymbol.Var, VROInt>,
        whole: Any,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): VROInt {
        return super.evalVar(interp, s, toStep, input, whole, l).addQualifier(VROQuals.MustEqual(s))
    }

    override fun evalEq(
        v1: VROInt,
        o1: TACSymbol,
        v2: VROInt,
        o2: TACSymbol,
        toStep: Map<TACSymbol.Var, VROInt>,
        input: Map<TACSymbol.Var, VROInt>,
        whole: Any,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): VROInt {
        if(!Config.EnabledEqualityReasoning.get()) {
            return super.evalEq(v1, o1, v2, o2, toStep, input, whole, l)
        }
        /**
         * Find all variables/symbols known to be equal o1
         */
        val v1Saturated = toStep.saturate(
            sym = o1,
        )

        /**
         * Ibid, for o2
         */
        val v2Saturated = toStep.saturate(
            sym = o2,
        )

        /**
         * Find those variables that must not be equal to any of the variables in v2's equivalence class.
         * This follows from the basic logic of v' == v2 /\ v' != v'' then v2 != v''.
         */
        val v2MustNot by lazy {
            v2Saturated.flatMapToSet {
                toStep.interp(it).qual.mapNotNullToTreapSet {
                    (it as? VROQuals.MustNotEqual)?.other
                }
            }
        }

        /**
         * As above, but with v1's equivalence class
         */
        val v1MustNot by lazy {
            v1Saturated.flatMapToSet {
                toStep.interp(it).qual.mapNotNullToTreapSet {
                    (it as? VROQuals.MustNotEqual)?.other
                }
            }
        }
        return super.evalEq(v1, o1, v2, o2, toStep, input, whole, l).let {
            /**
             * If v1's equivalence class overlaps v2's, then they must be equal, set the value to be true
             */
            if(v1Saturated.containsAny(v2Saturated)) {
                it.copy(
                    x = OpenInterval(BigInteger.ONE)
                )
            /**
             * If v1's equivalence class contains any variables that must not be equal to v2's must not equals, then this
             * expression must be false, and vice versa.
             * that is, from v1 == v' /\ v'' == v2 /\ v' != v'' we conclude v1 != v2, and this eq expression must be false.
             */
            } else if(v1Saturated.containsAny(v2MustNot) || v2Saturated.containsAny(v1MustNot)) {
                it.copy(
                    x = OpenInterval(BigInteger.ZERO)
                )
            } else {
                it
            }
        }
    }

}
