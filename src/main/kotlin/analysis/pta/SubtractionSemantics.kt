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

import analysis.LTACCmd
import analysis.numeric.IntQualifier
import analysis.numeric.IntValue
import evm.MAX_EVM_UINT256
import utils.containsAny
import vc.data.TACSymbol
import java.math.BigInteger

abstract class SubtractionSemantics<T>(private val symInterpreter: SymInterpreter<PointsToGraph, VPointsToValue>) {
    abstract val nondetInteger: T
    abstract val scratchPointerResult: T
    protected abstract fun lengthOfBlock(arrayPtr: Set<TACSymbol.Var>, pstate: PointsToDomain, where: LTACCmd) : T

    private fun PointsToGraph.interp(op1: TACSymbol, where: LTACCmd) = symInterpreter.interpSymbol(where, this, op1)

    fun subtractionSemantics(op1: TACSymbol, op2: TACSymbol, pstate: PointsToDomain, where: LTACCmd) : T {
        if(op1 is TACSymbol.Var && op2 is TACSymbol.Var) {
            val endPointerArr = pstate.boundsAnalysis[op1]?.tryResolve()?.let { it as? QualifiedInt }?.qual?.filterIsInstance(IntQualifier.EndOfArraySegment::class.java)?.map { it.arrayVar }
            if(endPointerArr != null) {
                val other = pstate.arrayState[op2]?.let { it as? ArrayStateAnalysis.Value.ElementPointer }?.takeIf { it.index == IntValue.Constant(BigInteger.ZERO) }?.arrayPtr
                if(other != null && endPointerArr.containsAny(other)) {
                    return lengthOfBlock(arrayPtr = other.union(endPointerArr), pstate = pstate, where = where)
                }
                val elemPtr = pstate.arrayState[op2]?.let { it as? ArrayStateAnalysis.WithIndexVars }?.takeIf { endPointerArr.containsAny(it.arrayPtr) }
                if(elemPtr != null) {
                    return untilEndProof(elemPtr = op2, pstate = pstate, where = where)
                }
            }
            val elementPointer = pstate.boundsAnalysis[op1]?.tryResolve()?.let { it as? QualifiedInt }?.qual?.filterIsInstance<IntQualifier.SizeOfElementSegment>()?.map { it.arrayVar }?.takeIf { it.isNotEmpty() }
            if(elementPointer != null) {
                return remainingSizeProof(indexPointer = op2, array = elementPointer, pstate = pstate, where = where)
            }
            pstate.arrayState[op1]?.tryResolve()?.let { aSt1 ->
                pstate.arrayState[op2]?.tryResolve()?.let { aSt2 ->
                    if(aSt1 is ArrayStateAnalysis.Value.ScratchPointer && aSt2 is ArrayStateAnalysis.Value.ScratchPointer) {
                        if(aSt1.index.getLowerBound() >= aSt2.index.getUpperBound()) {
                            // compute a range on this
                            val ub = aSt1.index.ub - aSt2.index.lb
                            val lb = aSt1.index.lb - aSt2.index.ub
                            return this.numericResult(lb, ub)
                        }
                    } else if(aSt2 is ArrayStateAnalysis.Value.ArrayBasePointer &&
                            aSt1 is ArrayStateAnalysis.Value.ElementPointer &&
                            pstate.pointsToState.store[op2]?.let {
                                it as? InitializationPointer.ByteInitPointer
                            }?.v?.addr?.let {a1 ->
                                a1 == pstate.pointsToState.store[op1]?.let {
                                    it as? InitializationPointer.ByteInitPointer
                                }?.v?.addr
                            } == true) {
                        val lb = (aSt1.index.lb + 32.toBigInteger()).min(MAX_EVM_UINT256)
                        val ub = (aSt1.index.ub + 32.toBigInteger()).min(MAX_EVM_UINT256)
                        return this.numericResult(lb,  ub)
                    } else if(aSt1 is ArrayStateAnalysis.Value.ElementPointer && aSt2 is ArrayStateAnalysis.Value.ElementPointer &&
                            aSt1.arrayPtr.containsAny(aSt2.arrayPtr) && symInterpreter.interpSymbol(where = where, sym = op1, st = pstate.pointsToState).let {
                                it is InitializationPointer.ByteInitPointer
                            }) {
                        val lb = aSt1.index.lb - aSt2.index.ub
                        val ub = aSt1.index.ub - aSt2.index.lb
                        return if(lb > BigInteger.ZERO && ub > BigInteger.ZERO && lb <= ub) {
                            this.numericResult(lb,  ub)
                        } else {
                            nondetInteger
                        }
                    }
                }
            }
        }
        return pstate.pointsToState.interp(op1, where).let { av1 ->
            if (av1 is ScratchPointer) {
                pstate.pointsToState.interp(op2, where).let { av2 ->
                    if(av2 is ScratchPointer) {
                        this.nondetInteger
                    } else {
                        this.scratchPointerResult
                    }
                }
            } else {
                this.numericSubtraction(op1, op2, pstate, where)
            }
        } ?: nondetInteger
    }

    open protected fun remainingSizeProof(
        indexPointer: TACSymbol.Var,
        array: List<TACSymbol.Var>,
        pstate: PointsToDomain,
        where: LTACCmd
    ): T = nondetInteger

    open protected fun untilEndProof(elemPtr: TACSymbol.Var, pstate: PointsToDomain, where: LTACCmd): T = nondetInteger

    open protected fun numericResult(lb: BigInteger, ub: BigInteger): T = nondetInteger

    protected abstract fun numericSubtraction(op1: TACSymbol, op2: TACSymbol, pstate: PointsToDomain, where: LTACCmd): T
}