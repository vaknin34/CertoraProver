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
import analysis.ptaInvariant
import com.certora.collect.*
import datastructures.stdcollections.*
import evm.EVM_WORD_SIZE
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACKeyword
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * Automatically track indices for analyses whose state is a map from variables to some abstract domain of type [V].
 * Some subset of the values in this domain will track indices, the common supertype of all of these values of interest
 * is [T], which must implemented [WithIndexing].
 *
 * Finally, in tracking and consuming index information, implementers may generate new facts that can be
 * consumed by other analyses. The type of these hints is [D] (can be [Nothing] if no such hints are generated)
 */
abstract class IndexTracking<V : Any, T, D>(private val numericDomain: NumericAnalysis) : ConstVariableFinder, Interpolator where T: WithIndexing<V> {
    fun stepCommand(m: TreapMap<TACSymbol.Var, V>, ltacCmd: LTACCmd, p: PointsToDomain): TreapMap<TACSymbol.Var, V> {
        if (ltacCmd.cmd !is TACCmd.Simple.AssigningCmd.AssignExpCmd || ltacCmd.cmd.rhs !is TACExpr.Sym)  {
            return m
        }
        val asConst = numericDomain.interpAsUnambiguousConstant(p, value = ltacCmd.cmd.rhs.s, ltacCmd = ltacCmd)
        return m.updateValues { k, v ->
            val t = downcast(v) ?: return@updateValues v
            ptaInvariant(v === t) {
                "downcasting $k @ $ltacCmd yielded an object with a different identity"
            }
            /**
             * Generally speaking we do not want to use mem0 or mem32 as indices...
             *
             * Remember that these are scalarized memory locations, and it is utterly implausible that solidity is tracking
             * an array index in the scratch memory.
             *
             * Further, if we do pull these in as indices, it means that copies into memory (which kill the tacM0x0 and tacM0x32)
             * end up rippling through our stack state, which is not at all desirable.
             */
            if(k == ltacCmd.cmd.lhs || ltacCmd.cmd.lhs == TACKeyword.MEM0.toVar() || ltacCmd.cmd.lhs == TACKeyword.MEM32.toVar()) {
                return@updateValues v
            }
            val isIndex = (t.constIndex != null && asConst != null && t.constIndex == asConst) || ltacCmd.cmd.rhs.s in t.indexVars
            val untilEndFor = untilEndFor(k, v, m, p, ltacCmd)
            val isUntilEnd = (untilEndFor != null && asConst == untilEndFor) || ltacCmd.cmd.rhs.s in t.untilEndVars
            if(!isIndex && !isUntilEnd) {
                return@updateValues v
            }
            val l = listOf(ltacCmd.cmd.lhs)
            val untilEnd = if(isUntilEnd) l else listOf()
            val index = if(isIndex) l else listOf()
            t.withVars(index, untilEnd)
        }
    }

    abstract protected fun indexStepSizeFor(k: TACSymbol.Var, v: V, m: Map<TACSymbol.Var, V>, p: PointsToDomain) : BigInteger?

    /**
     * Effectively reify the `as? T` operation into code. If [v] is not a subtype of T, return null, otherwise, return
     * the object unchanged.
     */
    abstract protected fun downcast(v: V) : T?

    /**
     * Some analyses that track indices may have a constant bound on the size of object being iterated over. If it
     * can be precisely computed how many (logical) elements remain until the end of the object, this function should
     * return that number (NOT the number of bytes). By default this function returns null, in which case the iterable
     * passed for the `untilEndVars` argument of [WithIndexing.withVars] will always be empty
     */
    open protected fun untilEndFor(k: TACSymbol.Var, t: V, m: Map<TACSymbol.Var, V>, p: PointsToDomain, ltacCmd: LTACCmd): BigInteger? = null

    /**
     * During interpolation, this class may conclude that a non-zero number of elements remain until the end of the tracked
     * object (i.e., if untilEndFor returns a value greater than zero, or any of the [WithIndexing.untilEndVars]
     * are provably non-zero). In this case, this class will call this function to "strengthen" the information represented
     * by [t] (e.g., to promote a "maybe valid index" into a "definitely valid index").
     */
    open protected fun strengthen(t: T) : T = t

    /**
     * As in the [strengthen], if this class determines there are indices remaining until the end of the object, this
     * may generate hints for other analyses in addition to the strengthening performed by [strengthen]. In this case,
     * this function is called.
     */
    open protected fun toValidHint(k: TACSymbol.Var, v: V) : D? = null

    open protected fun fieldStepSizeFor(
        k: TACSymbol.Var,
        v: V,
        m: Map<TACSymbol.Var, V>,
        p: PointsToDomain
    ) : BigInteger? = EVM_WORD_SIZE

    fun interpolate(
            prevM: TreapMap<TACSymbol.Var, V>,
            nextM: TreapMap<TACSymbol.Var, V>,
            next: PointsToDomain,
            summary: Map<TACSymbol.Var, TACExpr>
    ): Pair<TreapMap<TACSymbol.Var, V>, List<D>> {
        val conv = mutableListOf<D>()
        return nextM.updateValues { k, nextV ->
            val nextT = downcast(nextV) ?: return@updateValues nextV
            val prevT = prevM[k]?.let(this::downcast) ?: return@updateValues nextV
            if (nextT.indexVars.containsAll(prevT.indexVars) && nextT.untilEndVars.containsAll(prevT.untilEndVars)) {
                return@updateValues nextV
            }
            val fieldSize = fieldStepSizeFor(k, nextV, nextM, next) ?: return@updateValues nextV
            val isFieldStep = summary[k]?.let {
                isAddKTo(it, k, fieldSize)
            } ?: false
            if (!isFieldStep) {
                return@updateValues nextV
            }
            val stepSize = indexStepSizeFor(k, nextV, nextM, next) ?: return@updateValues nextV
            val toAddUntilEnd = prevT.untilEndVars.filter {
                summary[it]?.let {
                    it as? TACExpr.BinOp.Sub
                }?.let { s ->
                    s.operandsAreSyms() && s.o1 is TACExpr.Sym.Var && s.o1.s == it && s.o2 is TACExpr.Sym.Const && s.o2.s.value == stepSize
                } ?: false
            }
            val toAddIndex = prevT.indexVars.filter {
                isAddKTo(summary[it], it, stepSize)
            }
            // can we strengthen the sort?
            val t = if(toAddUntilEnd.any {
                        next.boundsAnalysis[it]?.let { it as? QualifiedInt }?.x?.isDefinitelyGreaterThan(BigInteger.ZERO) ?: false
                    }) {
                toValidHint(k, nextV)?.let(conv::add)
                strengthen(nextT)
            } else {
                nextT
            }
            t.withVars(
                    addIndex = toAddIndex,
                    addUntilEnd = toAddUntilEnd
            )
        } to conv
    }
}
