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

package analysis.pta

import analysis.alloc.AllocationAnalysis
import analysis.numeric.IntValue
import utils.`to?`
import vc.data.TACExpr
import vc.data.TACSymbol

abstract class LoopValueSummaryInterpreter<S, V> {
    /* Get bounds for non reference-value operands in the [valueSummary] definition if it has the form
     * X := Y + Z + ...
     * i.e. X := [scratch] + Y, then return the bounds for Y
     */
    private fun weaklyIncreasingIncrementBound(ref: TACSymbol.Var, valueSummary: LoopCopyAnalysis.LoopValueSummary.WeaklyIncreasing, bounds: NumericDomain ): IntValue? =
        when (val def = valueSummary.definition) {
            is TACExpr.Vec.Add ->
                def.ls.takeIf {
                    it.size == 2
                }?.filter {
                    when (it) {
                        is TACExpr.Sym.Var -> it.s != ref
                        else -> true
                    }
                }?.singleOrNull()?.let {
                    (it as? TACExpr.Sym.Var)?.let { v ->
                       bounds[v.s]?.expectInt()?.x
                    }
                }

            else -> null
        }

    fun interpretLoopSummary(s: Map<TACSymbol.Var, LoopCopyAnalysis.LoopValueSummary>, target: S, p: PointsToDomain): List<Pair<TACSymbol.Var, V>> {
        val (havocs, increase) = s.entries.partition { it.value is LoopCopyAnalysis.LoopValueSummary.Havoc }
        return increase.mapNotNull { entry ->
            if(entry.value == LoopCopyAnalysis.LoopValueSummary.Identity) {
                return@mapNotNull null
            }

            // For each source, if it's a reference value of some type then get the value of incrementing it
            entry.key to ((entry.value as LoopCopyAnalysis.LoopValueSummary.WeaklyIncreasing).src.mapNotNull {
                it `to?` p.pointsToState.store[it]?.let { it as? ReferenceValue }
            }.singleOrNull()?.let { (sym, it) ->
                val increment = weaklyIncreasingIncrementBound(sym, entry.value as LoopCopyAnalysis.LoopValueSummary.WeaklyIncreasing, p.boundsAnalysis)
                when (it) {
                    is InitializationPointer.ByteInitPointer -> {
                        if (it.initAddr.sort is AllocationAnalysis.Alloc.PackedByteArray) {
                            incrementPackedByte(sym, increment, target, it)
                        } else {
                            havocInt
                        }
                    }
                    is ScratchPointer -> scratchIncrement(sym, increment, target)
                    else -> havocInt
                }
            } ?: havocInt)
        } + havocs.map {
            it.key to havocInt
        }
    }

    abstract protected fun scratchIncrement(sourcePointer: TACSymbol.Var, increment: IntValue?, target: S): V
    abstract protected val havocInt: V
    abstract protected fun incrementPackedByte(it: TACSymbol.Var, increment: IntValue?, target: S, init: InitializationPointer.ByteInitPointer): V
}
