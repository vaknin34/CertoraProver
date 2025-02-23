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
import analysis.numeric.OpenInterval
import analysis.numeric.PathInformation
import analysis.numeric.QualifierPropagationComputation
import com.certora.collect.*
import evm.MAX_EVM_UINT256
import tac.Tag
import vc.data.TACMeta
import vc.data.TACSymbol
import vc.data.find
import java.math.BigInteger

/**
 * Qualifier propagation that handles [VROInt] and the qualifiers. In particular, it generates [analysis.opt.numeric.VROQuals.MustEqual]
 * qualifiers from propagating `x == y`, [analysis.opt.numeric.VROQuals.MustNotEqual] from `x != y` but only for contract
 * address variables, and [analysis.opt.numeric.VROQuals.WeakLowerBound] from lower bounds. Otherwise uses the logic
 * present in [QualifierPropagationComputation].
 */
open class VROQualifierPropagation : QualifierPropagationComputation<VROInt, Map<TACSymbol.Var, VROInt>, Any, VROQuals>() {
    override fun extractValue(op1: TACSymbol.Var, s: Map<TACSymbol.Var, VROInt>, w: Any, l: LTACCmd): VROInt {
        return s[op1] ?: if(op1.tag == Tag.Int) {
            VROInt.nondetFull
        } else {
            VROInt.nondet256
        }
    }

    override fun strictEquality(
        toRet: TACSymbol.Var,
        v: MutableList<PathInformation<VROQuals>>,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: Map<TACSymbol.Var, VROInt>,
        w: Any,
        l: LTACCmd
    ) {
        super.strictEquality(toRet, v, sym, num, s, w, l)
        val currValuation = extractValue(toRet, s, w, l).x
        val otherBound = num?.let(::OpenInterval) ?: sym?.let { extractValue(it, s, w, l) }?.x!!
        val lb = maxOf(currValuation.interval.low, otherBound.interval.low)
        val ub = minOf(currValuation.interval.high, otherBound.interval.high)
        if(ub < lb) {
            return // weird
        }
        lb.nOrNull()?.let { lbConst ->
            v.add(PathInformation.WeakLowerBound(sym = null, num = lbConst))
        }
        ub.nOrNull()?.let { ubConst ->
            v.add(PathInformation.WeakUpperBound(sym = null, num = ubConst))
        }
        sym?.let(s::get)?.qual?.map {
            PathInformation.Qual(it)
        }?.let(v::addAll)
        if(sym != null) {
            v.add(PathInformation.Qual(VROQuals.MustEqual(sym)))
        }
    }

    override fun strictInequality(
        toRet: TACSymbol.Var,
        v: MutableList<PathInformation<VROQuals>>,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: Map<TACSymbol.Var, VROInt>,
        w: Any,
        l: LTACCmd
    ) {
        if(num == BigInteger.ZERO) {
            v.add(PathInformation.StrictLowerBound(sym = null, num = BigInteger.ZERO))
        }
        s[toRet]?.qual?.filterIsInstance<VROQuals.SignExtended>()?.forEach { (extendedBit) ->
            val negatedMask = MAX_EVM_UINT256.andNot(BigInteger.TWO.pow(extendedBit) - BigInteger.ONE)
            if(num == negatedMask) {
                v.add(PathInformation.Qual(VROQuals.Negatable(extendedBit = extendedBit)))
            }
        }
    }

    override fun propagateNe(
        op1: TACSymbol,
        op2: TACSymbol,
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<VROQuals>>>,
        s: Map<TACSymbol.Var, VROInt>,
        w: Any,
        l: LTACCmd
    ): Boolean {
        return super.propagateNe(op1, op2, toRet, s, w, l) && run {
            if(op1 is TACSymbol.Const && op1.value == BigInteger.ZERO && op2 is TACSymbol.Var) {
                this.addPathInformation(toRet, op2) { pathInfo ->
                    pathInfo.add(PathInformation.StrictLowerBound(sym = null, num = BigInteger.ZERO))
                }
            }
            if(op2 is TACSymbol.Const && op2.value == BigInteger.ZERO && op1 is TACSymbol.Var) {
                this.addPathInformation(toRet, op1) { pathInfo ->
                    pathInfo.add(PathInformation.StrictLowerBound(sym = null, num = BigInteger.ZERO))
                }
            }
            if(op2 is TACSymbol.Var && op1 is TACSymbol.Var && op1.meta.find(TACMeta.CONTRACT_ADDR_KEY) != null) {
                this.addPathInformation(toRet, op2) { pathInfo ->
                    pathInfo.add(PathInformation.Qual(VROQuals.MustNotEqual(op1)))
                }
            }
            if(op1 is TACSymbol.Var && op2 is TACSymbol.Var && op2.meta.find(TACMeta.CONTRACT_ADDR_KEY) != null) {
                this.addPathInformation(toRet, op1) { pathInfo ->
                    pathInfo.add(PathInformation.Qual(VROQuals.MustNotEqual(op2)))
                }
            }
            true
        }
    }

    override fun strictLowerBound(
        toRet: TACSymbol.Var,
        v: MutableList<PathInformation<VROQuals>>,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: Map<TACSymbol.Var, VROInt>,
        w: Any,
        l: LTACCmd
    ) {
        if(sym != null) {
            addWeakLowerBoundQual(v, sym)
        }
    }

    private fun addWeakLowerBoundQual(v: MutableList<PathInformation<VROQuals>>, sym: TACSymbol.Var) {
        v.add(PathInformation.Qual(VROQuals.WeakLowerBound(sym)))
    }

    override fun weakLowerBound(
        toRet: TACSymbol.Var,
        v: MutableList<PathInformation<VROQuals>>,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: Map<TACSymbol.Var, VROInt>,
        w: Any,
        l: LTACCmd
    ) {
        if(sym != null) {
            addWeakLowerBoundQual(v, sym)
        }
    }
}
