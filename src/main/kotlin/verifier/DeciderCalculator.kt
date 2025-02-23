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

package verifier

import analysis.CmdPointer
import analysis.DagDefExprDataFlow
import analysis.LTACVar
import com.certora.collect.*
import datastructures.add
import datastructures.buildMultiMap
import utils.*
import vc.data.CoreTACProgram
import vc.data.TACExpr
import vc.data.TACSymbol
import verifier.DeciderCalculator.ConstantMakers
import verifier.DeciderCalculator.ConstantMakers.Ignore
import verifier.DeciderCalculator.ConstantMakers.VSet
import java.math.BigInteger


/**
 * Calculates for each expression in [code], what variables, if constant, would make this expression into a
 * constant. For example:
 * ```
 *    a := b * 3
 * ```
 * If `b` is a constant, then `a` will be too. We term this as `b` decides `a`.
 *
 * Analysis happens after calling [go], and then results can be queried as in [DagDefExprDataFlow]. Note that a variable
 * in the resulting set is paired with a [CmdPointer], which indicates where this variable should be a constant for this
 * to happen.
 */
class DeciderCalculator(code: CoreTACProgram) : DagDefExprDataFlow<ConstantMakers>(code) {

    /**
     *  Used to say which variables can make the expression in question (not seen here) into a constant.
     *  So if [set] is `{(ptr1, a), (ptr2, b)}`, then if `a` is a constant at `ptr1`, or `b` is a constant
     *  at `ptr2`, then we'd get a constant.
     */
    sealed interface ConstantMakers {
        val set: TreapSet<LTACVar>

        /** The expression is meaningless (i.e. a constant) */
        data object Ignore : ConstantMakers {
            override val set get() = error("Ignore doesn't have a set")
        }
        data class VSet(override val set: TreapSet<LTACVar> = treapSetOf()) : ConstantMakers

        val setOrNull get() = (this as? VSet)?.set
    }

    /**
     * uninitialized variables, are considered as if nothing can make them into a constant. but that is
     * what is attached to a lhs variable.
     */
    override fun uninitialized(v: TACSymbol.Var) = VSet()

    override fun handleConst(i: BigInteger) = Ignore

    /**
     * when looking at a variable on the rhs of an expression, all the info from def sites is collected,
     * but the variable itself, at this [ptr], is also in the set.
     */
    override fun normalizeRhs(ptr: CmdPointer, v: TACSymbol.Var, t: ConstantMakers) =
        VSet(t.setOrNull.orEmpty() + LTACVar(ptr, v))

    /**
     * intersects the sets, because if a `x`'s usage has two def sites, then to make it a constant
     * by setting another variable `y`, will require `x` to be set to a constant by `y` in both its def sites.
     */
    private fun joinSets(set1: TreapSet<LTACVar>, set2: TreapSet<LTACVar>): TreapSet<LTACVar> {
        val keys = set1.mapToSet { it.v }.apply { retainAll(set2.mapToSet { it.v }) }
        if (keys.isEmpty()) {
            return treapSetOf()
        }
        fun byVar(ltacVars: Set<LTACVar>) = buildMultiMap {
            for ((ptr, v) in ltacVars) {
                if (v in keys) {
                    add(v, ptr)
                }
            }
        }

        val map1 = byVar(set1)
        val map2 = byVar(set2)
        return buildTreapSet {
            for (v in keys) {
                for (ptr1 in map1[v]!!) {
                    for (ptr2 in map2[v]!!) {
                        // intersection must consider equivalent cases.
                        if (def.source(ptr1, v) == def.source(ptr2, v)) {
                            add(LTACVar(ptr1, v))
                        }
                    }
                }
            }
        }
    }

    override fun join(t1: ConstantMakers, t2: ConstantMakers) =
        when {
            t1 is Ignore -> t2
            t2 is Ignore -> t1
            else -> VSet(joinSets(t1.set, t2.set))
        }

    /**
     * if all non-const arguments can be made into constants by the same var, then it can make the
     * whole expression into a constant.
     */
    override fun handleExpr(ptr: CmdPointer, e: TACExpr, values: List<ConstantMakers>) =
        values
            .mapNotNull { it.setOrNull }
            .foldFirstOrNull(::joinSets)
            ?.let(::VSet)
            ?: Ignore
}

