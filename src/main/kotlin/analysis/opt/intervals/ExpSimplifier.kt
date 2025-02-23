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

package analysis.opt.intervals

import analysis.CmdPointer
import analysis.opt.ConstantPropagatorAndSimplifier.Companion.simplifyTop
import analysis.opt.ConstantPropagatorAndSimplifier.Companion.simplifyTopOrNull
import analysis.opt.intervals.ExtBig.Companion.Int256max
import analysis.opt.intervals.ExtBig.Companion.Int256minMath
import analysis.opt.intervals.ExtBig.Companion.MaxUInt
import analysis.opt.intervals.ExtBig.Companion.Zero
import analysis.opt.intervals.ExtBig.Companion.asExtBig
import analysis.opt.intervals.Intervals.Companion.SEmpty
import analysis.opt.intervals.Intervals.Companion.SFalse
import analysis.opt.intervals.Intervals.Companion.STrue
import analysis.opt.intervals.Intervals.Companion.eqAsConsts
import analysis.opt.intervals.Intervals.Companion.plusAll
import analysis.opt.intervals.Intervals.Companion.timesAll
import analysis.opt.intervals.IntervalsCalculator.Companion.calcOneVarExpression
import analysis.opt.intervals.IntervalsCalculator.Companion.intervalOfTag
import analysis.split.Ternary.Companion.isPowOf2Minus1
import datastructures.stdcollections.*
import evm.EVM_MOD_GROUP256
import evm.from2s
import evm.lowOnes
import evm.to2s
import tac.Tag
import utils.*
import vc.data.*
import vc.data.tacexprutil.rebuild
import java.math.BigInteger
import analysis.opt.intervals.Intervals as S

/**
 * There are quite a number of simplifications we can do when we have some knowledge of the values expressions
 * can take. This is where this simplification is done.
 *
 * [stats] counts the simplifications we do. See [IntervalsRewriter.stats].
 */
class ExpSimplifer(
    private val ptr: CmdPointer,
    private val intervals: IntervalsCalculator,
    private val stats: SimpleCounterMap<String>,
    private val txf: TACExprFact,
    private val preserve: (TACSymbol.Var) -> Boolean
) {
    /** Returns the resulting expression and the `Intervals` we know about it */
    fun simplify(e: TACExpr): Pair<TACExpr, S> {
        if (e is TACExpr.Sym.Const) {
            return e to S(e.s.value)
        }

        fun ofVar(v: TACSymbol.Var) =
            if (preserve(v)) {
                intervalOfTag(v.tag)
            } else {
                intervals.getS(ptr, v)
            }

        if (e is TACExpr.Sym.Var) {
            val i = ofVar(e.s)
            return if (i.isConst) {
                stats.plusOne("inlining")
                i.asConst.asTACExpr(e.tagAssumeChecked) to i
            } else {
                e to i
            }
        }

        calcOneVarExpression(e)?.let { (v, calculated) ->
            val known = ofVar(v)
            when (calculated intersect known) {
                known -> return txf.True to STrue // `e` has no additional constraints
                SEmpty -> return txf.False to SFalse // `e` contradicts the constraints we already have
                else -> Unit // fall back. There's probably something better to do here.
            }
        }

        // It's important to note that we don't use the intervals we know about inner expressions, we just use what we
        // know about the variables and forward calculations.
        // We may want to improve that in the future.
        val ops = e.getOperands()
        val (simpOps, intervals) = ops.map(::simplify).unzip()
        val i = ForwardCalculator.flatEval(e, intervals)

        if (i.isConst) {
            stats.plusOne("const")
            return i.asConst.asTACExpr(e.tagAssumeChecked) to i
        }

        // from this point on, we know the result is not known to be a constant, so no need to consider these cases.

        fun incStats() =
            stats.plusOne(
                if (e is TACExpr.Apply) {
                    (e.f as? TACExpr.TACFunctionSym.BuiltIn)?.bif?.name ?: "Apply"
                } else {
                    e.javaClass.canonicalName
                }
            )

        val newE = when (e) {
            is TACExpr.BinOp -> handleBinOp(e, simpOps, intervals)
            is TACExpr.TernaryExp -> handleTernary(e, simpOps, intervals)
            is TACExpr.BinBoolOp -> handleBinBoolOp(e, simpOps, intervals)
            is TACExpr.BinRel -> handleBinRel(e, simpOps, intervals)
            is TACExpr.UnaryExp -> handleUnary(e, simpOps, intervals)
            is TACExpr.Vec -> handleVec(e, simpOps, intervals)
            is TACExpr.Apply -> handleApply(e, simpOps, intervals)
            is TACExpr.LongStore -> handleLongStore(e, simpOps, intervals)
            is TACExpr.QuantifiedFormula -> null // This should be done as well.
            else -> null
        }?.let {
            incStats()
            simplifyTop(it)
        } ?: e.rebuild(simpOps).let { rebuilt ->
            simplifyTopOrNull(rebuilt)?.also { incStats() }
                ?: rebuilt
        }

        return newE to i
    }


    private fun handleBinOp(e: TACExpr, simpOps: List<TACExpr>, intervals: List<S>): TACExpr? {
        require(simpOps.size == 2)
        val (o1, o2) = simpOps
        val (i1, i2) = intervals

        /**
         * if one of the operands is known to be a constant, run
         *       [f](the constant, other operand, other operand intervals)
         * otherwise return null.
         */
        fun constFirst(f: (BigInteger, TACExpr, S) -> TACExpr?) =
            when {
                i1.isConst -> f(i1.asConst, o2, i2)
                i2.isConst -> f(i2.asConst, o1, i1)
                else -> null
            }

        return when (e) {
            is TACExpr.BinOp.BWAnd ->
                constFirst { mask, op, i ->
                    runIf(mask.isPowOf2Minus1 && i isLe mask.asExtBig) { op }
                }

            is TACExpr.BinOp.SignExtend -> {
                val bit = i1.asConstOrNull?.toIntOrNull()?.let { (it + 1) * 8 }
                    ?: return null
                runIf(i2.signExtend(bit) == i2) { o2 }
            }

            is TACExpr.BinOp.BWOr ->
                constFirst { c, op, i ->
                    when {
                        c == BigInteger.ZERO -> op

                        i isLe (lowOnes(c.lowestSetBit)).asExtBig ->
                            txf { safeMathNarrow(IntAdd(c.asTACExpr, op), Tag.Bit256) }

                        else -> null
                    }
                }

            is TACExpr.BinOp.BWXOr ->
                constFirst { c, op, i ->
                    when {
                        c == BigInteger.ZERO -> op

                        i isLe (lowOnes(c.lowestSetBit)).asExtBig ->
                            txf { safeMathNarrow(IntAdd(c.asTACExpr, op), Tag.Bit256) }

                        c.isPowOf2Minus1 && i isLe c.asExtBig ->
                            txf { safeMathNarrow(IntSub(c.asTACExpr, op), Tag.Bit256) }

                        else -> null
                    }
                }

            is TACExpr.BinOp.Sub ->
                when {
                    i2.asConstOrNull == BigInteger.ZERO -> o1
                    i1 isGe i2 -> txf { safeMathNarrow(IntSub(o1, o2), Tag.Bit256) }
                    else -> null
                }

            is TACExpr.BinOp.Mod ->
                when {
                    i1 isLt i2 && i1 isGe Zero -> o1
                    else -> null
                }

            is TACExpr.BinOp.SMod ->
                when {
                    i1 isSLt i2 -> o1
                    i1.isSurely2sNonNeg && i2.isSurely2sNonNeg -> txf.Mod(o1, o2)
                    else -> null
                }

            is TACExpr.BinOp.SDiv ->
                when {
                    i2.asConstOrNull == BigInteger.ONE -> o1
                    i1.isSurely2sNonNeg && i2.isSurely2sNonNeg -> txf.Div(o1, o2)
                    else -> null
                }

            is TACExpr.BinOp.ShiftLeft ->
                when {
                    i2.asConstOrNull == BigInteger.ZERO -> o1

                    // If x << y does not overflow, then we can save the mod256 by replacing with x * 2^y
                    i1.max.nOrNull()?.let { a ->
                        i2.max.nOrNull()?.toIntOrNull()?.let { b ->
                            b < 256 && a * BigInteger.TWO.pow(b) < EVM_MOD_GROUP256
                        }
                    } == true ->
                        txf {
                            val x = if (i2.isConst) {
                                BigInteger.TWO.pow(i2.asConst.toInt()).asTACExpr
                            } else {
                                Exponent(2.asTACExpr, o2)
                            }
                            safeMathNarrow(IntMul(o1, x), Tag.Bit256)
                        }

                    else -> null
                }

            else -> null
        }
    }


    private fun handleTernary(e: TACExpr.TernaryExp, simpOps: List<TACExpr>, intervals: List<S>): TACExpr? {
        require(simpOps.size == 3)
        val (o1, o2, _) = simpOps
        val (i1, i2, i3) = intervals

        return when (e) {
            is TACExpr.TernaryExp.Ite ->
                null

            is TACExpr.TernaryExp.AddMod ->
                (i1 + i2).let { sum ->
                    runIf(sum isGe Zero && sum isLt i3) {
                        simplify(txf { safeMathNarrow(IntAdd(o1, o2), Tag.Bit256) }).first
                    }
                }

            is TACExpr.TernaryExp.MulMod ->
                (i1 * i2).let { prod ->
                    runIf(prod isGe Zero && prod isLt i3) {
                        simplify(txf { safeMathNarrow(IntMul(o1, o2), Tag.Bit256) }).first
                    }
                }
        }
    }


    @Suppress("UNUSED_PARAMETER")
    private fun handleBinBoolOp(e: TACExpr.BinBoolOp, simpOps: List<TACExpr>, intervals: List<S>) = null

    private fun handleBinRel(e: TACExpr.BinRel, simpOps: List<TACExpr>, intervals: List<S>): TACExpr? {
        require(simpOps.size == 2)
        val (o1, o2) = simpOps
        val (i1, i2) = intervals

        fun sameSign() =
            (i1.isSurely2sNonNeg && i2.isSurely2sNonNeg) || (i1.isSurely2sNeg && i2.isSurely2sNeg)

        with(txf) {
            return when (e) {
                is TACExpr.BinRel.Sge -> runIf(sameSign()) { simplify(Ge(o1, o2)).first }
                is TACExpr.BinRel.Sgt -> runIf(sameSign()) { simplify(Gt(o1, o2)).first }
                is TACExpr.BinRel.Sle -> runIf(sameSign()) { simplify(Le(o1, o2)).first }
                is TACExpr.BinRel.Slt -> runIf(sameSign()) { simplify(Lt(o1, o2)).first }
                else -> null
            }
        }
    }


    @Suppress("UNUSED_PARAMETER")
    private fun handleUnary(e: TACExpr.UnaryExp, simpOps: List<TACExpr>, intervals: List<S>) = null

    private fun handleVec(e: TACExpr.Vec, simpOps: List<TACExpr>, intervals: List<S>): TACExpr? =
        when (e) {
            is TACExpr.Vec.Add ->
                filterOps(simpOps, intervals, BigInteger.ZERO).let { (ops, vals) ->
                    when {
                        ops.size == 1 -> ops.first()

                        plusAll(vals) isLt (e.tagAssumeChecked as Tag.Bits).modulus.asExtBig -> {
                            stats.plusOne("Add->IntAdd")
                            txf { safeMathNarrow(IntAdd(ops), e.tagAssumeChecked as Tag.Bits) }
                        }

                        ops.size == simpOps.size -> null

                        else -> txf.Add(ops)
                    }
                }

            is TACExpr.Vec.Mul ->
                filterOps(simpOps, intervals, BigInteger.ONE, txf.Zero).let { (ops, vals) ->
                    when {
                        ops.size == 1 -> ops.first()

                        timesAll(vals) isLt (e.tagAssumeChecked as Tag.Bits).modulus.asExtBig -> {
                            stats.plusOne("Mul->IntMul")
                            txf { safeMathNarrow(IntMul(ops), e.tagAssumeChecked as Tag.Bits) }
                        }

                        vals.size == 2 -> {
                            val m = vals[0].toMathInt() * vals[1].toMathInt()
                            runIf(m isGe Int256minMath && m isLe Int256max) {
                                stats.plusOne("Mul->SignedIntMul")
                                txf {
                                    val inner = IntMul(
                                        twosUnwrap(simpOps[0], vals[0], createAnyway = true)!!,
                                        twosUnwrap(simpOps[1], vals[1], createAnyway = true)!!
                                    )
                                    twosWrap(inner, m, createAnyway = true)!!
                                }
                            }
                        }

                        ops.size == simpOps.size -> null

                        else -> txf.Mul(ops)
                    }
                }

            else -> null
        }


    /**
     * Filter out from [ops] all the [neutral] elements according to [intervals] corresponding to [ops].
     * If [zeroing] is not null, then even if one of [intervals] is equal to it, then that is the returned
     * only value.
     *
     * The returned value is the pairs of resulting ops, together with their corresponding intervals.
     */
    private fun filterOps(
        ops: List<TACExpr>,
        intervals: List<S>,
        neutral: BigInteger,
        zeroing: TACExpr.Sym.Const? = null
    ): Pair<List<TACExpr>, List<S>> {
        require(ops.size == intervals.size)
        return (ops zip intervals).filterNot { (_, i) ->
            if (zeroing != null && i.asConstOrNull == zeroing.s.value) {
                return listOf(zeroing) to listOf(i)
            }
            i.asConstOrNull == neutral
        }.unzip()
    }


    /**
     * converts a mathint to a 2s complement bv256, but can simplify if it sees its not really needed.
     * [createAnyway] will create the expression even if there is no simplification, otherwise, null is returned.
     */
    private fun twosWrap(e: TACExpr, i: S, createAnyway: Boolean = false) =
        when {
            i.isConst -> i.asConst.to2s().asTACExpr
            i isGe Zero -> txf.safeMathNarrow(e, Tag.Bit256)
            i isLt Zero -> txf { safeMathNarrow(IntAdd(e, EVM_MOD_GROUP), Tag.Bit256) }
            else -> runIf(createAnyway) { txf.twosWrap(e) }
        }

    /**
     * converts a 2s complement bv256 to mathint, but can simplify if it sees its not really needed.
     * [createAnyway] will create the expression even if there is no simplification, otherwise, null is returned.
     */
    private fun twosUnwrap(e: TACExpr, i: S, createAnyway: Boolean = false) =
        when {
            i.isConst -> i.asConst.from2s().asTACExpr
            i.isSurely2sNonNeg -> e
            i.isSurely2sNeg -> txf { IntSub(e, EVM_MOD_GROUP) }
            else -> runIf(createAnyway) { txf.twosUnwrap(e) }
        }


    /** assuming s is in mathint form */
    private fun noSignedOverflow(s : S) =
        when {
            s isLt Int256minMath || s isGt Int256max -> txf.False
            s isGe Int256minMath && s isLe Int256max -> txf.True
            else -> null
        }


    private fun handleApply(e: TACExpr.Apply, simpOps: List<TACExpr>, vals: List<S>): TACExpr? =
        when ((e.f as? TACExpr.TACFunctionSym.BuiltIn)?.bif) {
            is TACBuiltInFunction.TwosComplement.Wrap ->
                twosWrap(simpOps[0], vals[0])

            is TACBuiltInFunction.TwosComplement.Unwrap ->
                twosUnwrap(simpOps[0], vals[0])

            is TACBuiltInFunction.NoAddOverflowCheck -> {
                val a = vals[0] + vals[1]
                when {
                    a isGt MaxUInt -> txf.False
                    a isLe MaxUInt -> txf.True
                    else -> null
                }
            }

            TACBuiltInFunction.NoMulOverflowCheck -> {
                val a = vals[0] * vals[1]
                when {
                    a isGt MaxUInt -> txf.False
                    a isLe MaxUInt -> txf.True
                    else -> null
                }
            }

            TACBuiltInFunction.NoSMulOverAndUnderflowCheck ->
                noSignedOverflow(vals[0].toMathInt() * vals[1].toMathInt())

            TACBuiltInFunction.NoSAddOverAndUnderflowCheck ->
                noSignedOverflow(vals[0].toMathInt() + vals[1].toMathInt())

            TACBuiltInFunction.NoSSubOverAndUnderflowCheck ->
                noSignedOverflow(vals[0].toMathInt() - vals[1].toMathInt())

            is TACBuiltInFunction.SafeMathPromotion ->
                simpOps.single()

            else -> null
        }


    private fun handleLongStore(e: TACExpr.LongStore, simpOps: List<TACExpr>, vals: List<S>): TACExpr? {
        // We are counting on the order of `getOperands`, which is: `dstMap, dstOffset, srcMap, srcOffset, length`

        // length is zero
        if (vals[4].asConstOrNull == BigInteger.ZERO) {
            return e.dstMap
        }

        // dstMap and srcMap are the same, and so are srcOffset and dstOffset.
        // this would be much better if comparison was augmented with gvn of def analysis.
        if (simpOps[0] == simpOps[2] && eqAsConsts(vals[1], vals[3])) {
            return e.dstMap
        }

        return null
    }

}
