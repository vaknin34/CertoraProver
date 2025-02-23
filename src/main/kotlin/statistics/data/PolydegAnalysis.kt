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

package statistics.data

import analysis.CmdPointer
import analysis.DagDefExprDataFlow
import tac.CallId
import utils.`impossible!`
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * Expects TACSimpleSimple.
 *
 * @param dataFlowsThroughMaps whether to assume that data flows through maps (memory, storage, ghost) since we
 *     don't want to use a pointer analysis here, this is all or nothing, i.e "everything/nothing may alias"
 * @param divAndModSum if true, div and mod lead to summation of the exponents, like "mul" does, otherwise it's the
 *     max operation, like "add"
 */
class PolydegAnalysis(
    prog: CoreTACProgram,
    val callIdsToJump: Set<CallId>? = null,
    val dataFlowsThroughMaps: Boolean = true,
    val divAndModSum: Boolean = false,
) : DagDefExprDataFlow<Int>(prog) {

    private val bottom = 1

    /** See class comment on [divAndModSum] */
    private val divAndModOp: Int.(Int) -> Int = if (divAndModSum) { Int::plus } else { ::maxOf }

    override fun join(t1: Int, t2: Int): Int = maxOf(t1, t2)

    private fun joinF(ts: List<Int>) = ts.fold(bottom, ::join)

    override fun handleConst(i: BigInteger): Int = 0

    override fun uninitialized(v: TACSymbol.Var): Int = bottom

    var maxDegree = 0

    override fun handleExpr(ptr: CmdPointer, e: TACExpr, values: List<Int>): Int {
        return if (callIdsToJump != null && ptr.block.calleeIdx in callIdsToJump) {
            bottom
        } else {
            val r = when (e) {
                is TACExpr.Vec.Add,
                is TACExpr.Vec.IntAdd -> joinF(values)

                is TACExpr.Vec.Mul,
                is TACExpr.Vec.IntMul -> values.sum()

                is TACExpr.BinOp.Sub,
                is TACExpr.BinOp.IntSub -> joinF(values)

                is TACExpr.BinOp.Mod,
                is TACExpr.BinOp.SMod,
                is TACExpr.BinOp.Div,
                is TACExpr.BinOp.IntDiv -> divAndModOp(values[0], values[1])

                is TACExpr.TernaryExp.Ite -> join(values[1], values[2])

                is TACExpr.TernaryExp.AddMod,
                is TACExpr.TernaryExp.MulMod -> {
                    val c1 = when (e) {
                        is TACExpr.TernaryExp.AddMod -> join(values[0], values[1])
                        is TACExpr.TernaryExp.MulMod -> values[0] + values[1]
                        else -> `impossible!`
                    }
                    divAndModOp(c1, values[2])
                }


                // for Store/Select, we're assuming "may equal" for all pairs of used `loc`s
                // not sure if we should do something about LongStore, not clear what, might be fine
                is TACExpr.Store -> {
                    // give the degree of `e.value` to the whole store expression
                    if (dataFlowsThroughMaps) {
                        join(values[0], values[2])
                    } else {
                        bottom
                    }
                }

                is TACExpr.Select -> {
                    // give the degree of `e.base` to the whole select expression
                    if (dataFlowsThroughMaps) {
                        values[0]
                    } else {
                        bottom
                    }
                }

                // hashes and Booleans we don't count as arithmetic constructs -- assigning "bottom" (which is 1)
                is TACExpr.SimpleHash,
                is TACExpr.UnaryExp.LNot,
                is TACExpr.BinBoolOp,
                is TACExpr.BinRel -> bottom

                else -> joinF(values)
            }
            maxDegree = maxOf(maxDegree, r)
            r
        }
    }

    override fun go() {
        super.go()
        // handleExpr will be called on every assigning command, but we need it to run on every expression, so:
        g.commands.forEach { (ptr, cmd) ->
            if (cmd is TACCmd.Simple.AssumeExpCmd) {
                rhsVal(ptr, cmd.cond)
            }
        }
    }

}
