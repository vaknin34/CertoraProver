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

import analysis.LTACCmd
import analysis.LTACCmdView
import com.certora.collect.*
import datastructures.stdcollections.*
import utils.*
import vc.data.TACCmd
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * Extend the semantics of [delegate] to track multiple and mask information in the qualifier domain [Q]
 * attached to an integer value approximation [I] that abstract integers with [T].
 *
 * The injection of masking and multiple information into [Q] is accomplished by way of the abstract
 * functions [maskedOf] and [multipleOf]
 */
abstract class BasicMathCombinator<in S, in W, @Treapable Q: Qualifier<Q>, I: QualifiedInt<I, T, Q>, T: IntApprox<T>>(
    private val delegate : IValueSemantics<S, I, W>,
) : IValueSemantics<S, I, W> by delegate {
    override fun evalBWAnd(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        return delegate.evalBWAnd(v1, o1, v2, o2, toStep, input, whole, l).let { res ->
            val multConsts = mutableSetOf<Q>()
            if(v2.x.isConstant) {
                val multOf = isModuloMask(v2.x.c)
                if(multOf != null) {
                    multipleOf(multOf)?.let(multConsts::add)
                }
                if(o1 is TACSymbol.Var && (v2.x.c + BigInteger.ONE).bitCount() == 1) {
                    maskedOf(v2.x.c.bitCount(), o1)?.let(multConsts::add)
                }
            }
            if(v1.x.isConstant) {
                isModuloMask(v1.x.c)?.let {
                    multipleOf(it)?.let(multConsts::add)
                }
                if(o2 is TACSymbol.Var && (v1.x.c + BigInteger.ONE).bitCount() == 1) {
                    maskedOf(v1.x.c.bitCount(), o2)?.let(multConsts::add)
                }
            }
            res.withQualifiers(res.qual + multConsts)
        }
    }

    abstract fun maskedOf(bitCount: Int, o2: TACSymbol.Var): Q?

    abstract fun multipleOf(multOf: BigInteger): Q?

    override fun evalAdd(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        val qual = mutableListOf<Q>()
        checkModulo(v1, v2, qual)
        checkModulo(v2, v1, qual)
        return delegate.evalAdd(v1, o1, v2, o2, toStep, input, whole, l).let {
            it.withQualifiers(it.qual + qual)
        }
    }

    private fun checkModulo(a1: I, a2: I, qual: MutableList<Q>) {
        if (a1.x.isConstant && (isMultipleOf(a2, a1.x.c))) {
            multipleOf(a1.x.c)?.let(qual::add)
        }
    }

    private fun isMultipleOf(a2: I, isModulo: BigInteger): Boolean {
        return isModulo > BigInteger.ZERO && (isModulo == BigInteger.ONE || ((a2.x.isConstant && a2.x.c.mod(isModulo) == BigInteger.ZERO) || a2.qual.any {
            it is IntQualifier.MultipleOf && it.factor == isModulo
        }))
    }

    private fun isModuloMask(c: BigInteger): BigInteger? {
        if (c <= BigInteger.ZERO) { // otherwise may get ArithmeticException in `testBit` either because the number is negative or because x is -1
            return null
        }
        val x = c.lowestSetBit
        for(it in x..255) {
            if(!c.testBit(it)) {
                return null
            }
        }
        return BigInteger.ONE.shiftLeft(x)
    }

    override fun evalMult(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        return delegate.evalMult(v1, o1, v2, o2, toStep, input, whole, l).let { res ->
            val q = mutableListOf<Q>()
            if (v1.x.isConstant && v1.x.c != BigInteger.ZERO) {
                multipleOf(v1.x.c)?.let(q::add)
            }
            if (v2.x.isConstant && v2.x.c != BigInteger.ZERO) {
                multipleOf(v2.x.c)?.let(q::add)
            }
            res.withQualifiers(res.qual + q)
        }
    }

    override fun evalShiftLeft(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return delegate.evalShiftLeft(v1, o1, v2, o2, toStep, input, whole, l).let { res ->
            if (v2.x.isConstant && v2.x.c != BigInteger.ZERO) {
                v2.x.c.toIntOrNull()?.let { intVal ->
                    multipleOf(BigInteger.TWO.pow(intVal))?.let { q ->
                        res.withQualifiers(res.qual + q)
                    }
                } ?: res
            } else {
                res
            }
        }
    }

    companion object {
        operator fun <S, W, @Treapable Q: Qualifier<Q>, I: QualifiedInt<I, T, Q>, T: IntApprox<T>> invoke(
            del: IValueSemantics<S, I, W>,
            fMultipleOf: (BigInteger) -> Q?,
            fMaskedOf: (TACSymbol.Var, Int) -> Q?
        ) = object : BasicMathCombinator<S, W, Q, I, T>(delegate = del) {
            override fun maskedOf(bitCount: Int, o2: TACSymbol.Var): Q? = fMaskedOf(o2, bitCount)

            override fun multipleOf(multOf: BigInteger): Q? = fMultipleOf(multOf)

        }
    }
}

/**
 * Extend a values semantics over integer approximations qualified with [Q] to track multiple and masking information.
 * [multipleOf] is a callback that should return a qualifier in [Q] that records a value is a multiple of the argument.
 * [maskedOf] records that a value is the result of applying a mask of the given width to the variable.
 */
fun <S, W, @Treapable Q: Qualifier<Q>, I: QualifiedInt<I, T, Q>, T: IntApprox<T>> IValueSemantics<S, I, W>.withBasicMath(
    multipleOf: (BigInteger) -> Q?,
    maskedOf: (TACSymbol.Var, Int) -> Q?
) = BasicMathCombinator(this, multipleOf, maskedOf)

/**
 * Extend the semantics of [delegate] to track path condition information in the qualifier domain [Q].
 * It is assumed (but not required) that some element of [Q] implement [ConditionQualifier] and [LogicalConnectiveQualifier].
 */
abstract class PathConditionQualifierInterpreter<in S, in W, @Treapable Q: Qualifier<Q>, I: QualifiedInt<I, T, Q>, T: IntApprox<T>>(
    private val delegate : IValueSemantics<S, I, W>,
) :IValueSemantics<S, I, W> by delegate {
    /**
     * Return a qualifier that records a value represents [op1] [cond] [op2].
     */
    abstract fun condition(cond: ConditionQualifier.Condition, op1: TACSymbol, op2: TACSymbol) : Q?

    /**
     * Return a qualifier that records a value represents that [op1] [connective] [op2].
     */
    abstract fun conjunction(connective: LogicalConnectiveQualifier.LBinOp, op1: TACSymbol.Var, op2: TACSymbol.Var) : Q?

    /**
     * Return a qualifier that represents the logical negation of the qualifier in [toFlip]. This should return null
     * if this can't be represented or if the qualifier doesn't represent logical information.
     */
    abstract fun flip(toFlip: Q) : Q?

    private fun mergeQualifier(r: I, q: Q?) : I {
        if(q == null) {
            return r
        }
        return r.withQualifiers(r.qual + q)
    }

    private fun mergeQualifiers(r: I, q: Q?, ext: Collection<Q>) : I {
        if(q == null && ext.isEmpty()) {
            return r
        }
        return r.withQualifiers(r.qual + ext + q?.let(::listOf).orEmpty())
    }

    private fun constantEvalConnective(
        v1: I, v2: I, otherMustBeTrue: (T) -> Boolean
    ) : Collection<Q> {
        val propagated = mutableSetOf<Q>()
        if(otherMustBeTrue(v1.x)) {
            propagated.addAll(v2.qual.filterLogical())
        }
        if(otherMustBeTrue(v2.x)) {
            propagated.addAll(v1.qual.filterLogical())
        }
        return propagated
    }


    override fun evalBWAnd(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        return delegate.evalBWAnd(v1, o1, v2, o2, toStep, input, whole, l).let { res ->
            if(isBoolLike(o1, v1) && isBoolLike(o2, v2)) {
                mergeQualifiers(
                    res,
                    conjunction(
                        op1 = o1 as TACSymbol.Var,
                        op2 = o2 as TACSymbol.Var,
                        connective = LogicalConnectiveQualifier.LBinOp.AND
                    ),
                    constantEvalConnective(v1, v2) {
                        !it.mayEqual(BigInteger.ZERO)
                    }
                )
            } else {
                res
            }
        }
    }

    protected open fun isBoolLike(o1: TACSymbol, v1: I) : Boolean {
        return o1 is TACSymbol.Var && v1.x.getUpperBound()?.let { ub -> ub <= BigInteger.ONE } == true && v1.x.getLowerBound()?.let { lb -> lb >= BigInteger.ZERO } == true
    }

    override fun evalBWOr(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return delegate.evalBWOr(v1, o1, v2, o2, toStep, input, whole, l).let {
            if(isBoolLike(o1, v1) && isBoolLike(o2, v2)) {
                mergeQualifiers(
                    it, conjunction(
                        connective = LogicalConnectiveQualifier.LBinOp.OR,
                        op1 = o1 as TACSymbol.Var,
                        op2 = o2 as TACSymbol.Var
                    ), constantEvalConnective(v1, v2) {
                        it.mustEqual(BigInteger.ZERO)
                    }
                )
            } else {
                it
            }
        }
    }

    private fun Collection<Q>.filterLogical() = this.mapNotNull {
        flip(it)?.let(::flip)
    }

    override fun evalLt(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return delegate.evalLt(v1, o1, v2, o2, toStep, input, whole, l).let { res ->
            val condQualifiers = if(v1.x.isConstant && v1.x.c == BigInteger.ZERO) {
                v2.qual.filterLogical()
            } else {
                listOf()
            }
            val imm = mergeQualifier(res, condition(op1 = o1, op2 = o2, cond = ConditionQualifier.Condition.LT))
            condQualifiers.fold(imm, ::mergeQualifier)
        }
    }

    override fun evalLe(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        return delegate.evalLe(v1, o1, v2, o2, toStep, input, whole, l).let { res ->
            mergeQualifier(res, condition(op1 = o1, op2 = o2, cond = ConditionQualifier.Condition.LE))
        }
    }

    override fun evalEq(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        val z = TACSymbol.lift(0)
        return delegate.evalEq(v1, o1, v2, o2, toStep, input, whole, l).let {
            val toAdd = mutableSetOf<Q>()
            condition(op1 = o1, op2 = o2, cond = ConditionQualifier.Condition.EQ)?.let(toAdd::add)
            if(o2 == z) {
                toAdd.addAll(flipConditions(v1))
            }
            if(o1 == z) {
                toAdd.addAll(flipConditions(v2))
            }
            if(toAdd.isEmpty()) {
                return@let it
            }
            it.withQualifiers(it.qual + toAdd)
        }
    }

    override fun evalLNot(v1: I, s: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        return delegate.evalLNot(v1, s, toStep, input, whole, l).let {
            it.withQualifiers(it.qual + this.flipConditions(v1))
        }
    }

    override fun evalSlt(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return delegate.evalSlt(v1, o1, v2, o2, toStep, input, whole, l).let {
            mergeQualifier(
                it, condition(
                    op1 = o1, op2 = o2, cond = ConditionQualifier.Condition.SLT
                )
            )
        }
    }

    /**
     * Generate a set of [IntQualifier] that are the logical negation of any conditional
     * qualifiers four in [a1]. This is called when the semantics discover a comparison to the constant 0, i.e.,
     * a logical negation.
     */
    protected open fun flipConditions(a1: I): Iterable<Q> {
        return a1.qual.mapNotNull {
            flip(it)
        }
    }

    override fun evalLAnd(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return delegate.evalLAnd(
            v1, o1, v2, o2, toStep, input, whole, l
        ).let {
            evalLogicalBinOp(
                conj = LogicalConnectiveQualifier.LBinOp.AND,
                it,
                o1,
                o2
            )
        }
    }

    open protected fun evalLogicalBinOp(
        conj: LogicalConnectiveQualifier.LBinOp,
        res: I,
        o1: TACSymbol,
        o2: TACSymbol
    ) : I {
        return if(o1 !is TACSymbol.Var || o2 !is TACSymbol.Var) {
            res
        } else {
            mergeQualifier(res, conjunction(
                    connective = conj,
                    op1 = o1,
                    op2 = o2
                )
            )
        }
    }

    override fun evalLOr(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return delegate.evalLOr(v1, o1, v2, o2, toStep, input, whole, l).let {
            evalLogicalBinOp(
                conj = LogicalConnectiveQualifier.LBinOp.OR,
                it,
                o1,
                o2
            )
        }
    }

    override fun evalIte(
        i: I,
        iSym: TACSymbol,
        t: I,
        tSym: TACSymbol,
        e: I,
        eSym: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        val tConst = t.x.takeIf { it.isConstant }?.c
        val eConst = e.x.takeIf { it.isConstant }?.c
        val del = delegate.evalIte(i, iSym, t, tSym, e, eSym, toStep, input, whole, l)
        if(!isBoolLike(iSym, i)) {
            return del
        }
        return if(tConst == BigInteger.ZERO && eConst == BigInteger.ONE) {
            del.withQualifiers(del.qual + i.qual.mapNotNull {
                    flip(it)
                }
            )
        } else if(tConst == BigInteger.ONE && eConst == BigInteger.ZERO) {
            del.withQualifiers(i.qual.filterLogical())
        } else {
            del
        }
    }

    override fun evalAdd(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        val logicalQuals = mutableListOf<Q>()
        if(v1.x.mustEqual(BigInteger.ZERO)) {
            logicalQuals.addAll(v2.qual.filterLogical())
        }
        if(v2.x.mustEqual(BigInteger.ZERO)) {
            logicalQuals.addAll(v1.qual.filterLogical())
        }
        return delegate.evalAdd(v1, o1, v2, o2, toStep, input, whole, l).let { del ->
            del.withQualifiers(del.qual + logicalQuals)
        }
    }

    companion object {
        operator fun <S, W, @Treapable Q: Qualifier<Q>, I: QualifiedInt<I, T, Q>, T: IntApprox<T>> invoke(
                del: IValueSemantics<S, I, W>,
        fCondition: (TACSymbol, TACSymbol, ConditionQualifier.Condition) -> Q?,
        fConjunction: (LogicalConnectiveQualifier.LBinOp, TACSymbol.Var, TACSymbol.Var) -> Q?,
                fFlip: (Q) -> Q?
        ) = object : PathConditionQualifierInterpreter<S, W, Q, I, T>(del) {
            override fun flip(toFlip: Q): Q? = fFlip(toFlip)

            override fun condition(cond: ConditionQualifier.Condition, op1: TACSymbol, op2: TACSymbol): Q? {
                return fCondition(op1, op2, cond)
            }

            override fun conjunction(
                connective: LogicalConnectiveQualifier.LBinOp,
                op1: TACSymbol.Var,
                op2: TACSymbol.Var
            ): Q? {
                return fConjunction(connective, op1, op2)
            }
        }
    }
}

/**
 * Extend the value semantics over a domain [I] qualified with [Q] to track path information.
 * [flip], [condition], and [conjunction] are used as the implementations for [PathConditionQualifierInterpreter.flip]
 * [PathConditionQualifierInterpreter.condition] and [PathConditionQualifierInterpreter.conjunction] respectively
 */
fun <S, W, @Treapable Q: Qualifier<Q>, I: QualifiedInt<I, T, Q>, T: IntApprox<T>> IValueSemantics<S, I, W>.withPathConditions(
    condition: (TACSymbol, TACSymbol, ConditionQualifier.Condition) -> Q?,
    conjunction: (LogicalConnectiveQualifier.LBinOp, TACSymbol.Var, TACSymbol.Var) -> Q?,
    flip: (Q) -> Q?
) = PathConditionQualifierInterpreter(
    this, condition, conjunction, flip
)

/**
 * If x is qualified by q and Q : ModularUpperBoundQualifier:
 *  then (x < q.other if q.strong else x <= q.other) AND (q.modulus divides q.other - x)
 */
interface ModularUpperBoundQualifier {
    val other: TACSymbol
    val modulus: BigInteger
    val strong: Boolean
}

/**
 * Add reasoning about modular upper bounds to [delegate].
 */
class ModularUpperBoundSemantics<S, W, M: ModularUpperBoundQualifier, @Treapable Q: Qualifier<Q>, I: QualifiedInt<I, T, Q>, T: IntApprox<T>>(
    private val delegate: IValueSemantics<S, I, W>,
    private val modularUpperBound: (TACSymbol, BigInteger, Boolean) -> Q?,
    private val extractModularUpperBound: (Q) -> M?,
): IValueSemantics<S, I, W>  by delegate {

    /**
     * If i1 : ModularUpperBound(x, m, strong) AND i2 == m, then return ModularUpperBound(x, m, weak)
     */
    private fun isUpperBoundShift(i1: I, i2: I): Iterable<Q> {
        if(!i2.x.isConstant) {
            return listOf()
        }
        return i1.qual.asSequence().mapNotNull(extractModularUpperBound).filter {
            it.strong && it.modulus == i2.x.c
        }.mapNotNull {
            modularUpperBound(it.other, it.modulus, false)
        }.asIterable()
    }

    // Propagates modular upper bounds according to the rule that
    // if i1 : ModularUpperBound(x, m, strong) AND i2 == m, then (i1 + i2) : ModularUpperBound(x, m, weak)
    override fun evalAdd(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        return delegate.evalAdd(v1, o1, v2, o2, toStep, input, whole, l).let { av ->
            val qs = isUpperBoundShift(v1, v2) + isUpperBoundShift(v2, v1)
            av.withQualifiers(av.qual + qs)
        }
    }

    override fun evalAddMod(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        v3: I,
        o3: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return delegate.evalAddMod(v1, o2, v2, o2, v3, o3, toStep, input, whole, l).let { av ->
            val sum = v1.x.getUpperBound()?.let { ub1 -> v2.x.getUpperBound()?.let { ub2 -> ub1 + ub2 } }
            val modLowerBound = v3.x.getLowerBound()
            if (sum == null || modLowerBound == null || sum >= modLowerBound) {
                return av
            }
            av.withQualifiers(
                av.qual + isUpperBoundShift(v1, v2) + isUpperBoundShift(v2, v1)
            )
        }
    }
}

fun <S, W, M: ModularUpperBoundQualifier, @Treapable Q: Qualifier<Q>, I: QualifiedInt<I, T, Q>, T: UIntApprox<T>> IValueSemantics<S, I, W>.withModularUpperBounds(
    modularUpperBound: (TACSymbol, BigInteger, Boolean) -> Q?,
    extractModularUpperBound: (Q) -> M?,
) = ModularUpperBoundSemantics(
    this,
    modularUpperBound,
    extractModularUpperBound
)

/**
 * Add reasoning about modular upper bounds to [delegate].
 */
class ModularUpperBoundPropagator<M: ModularUpperBoundQualifier, I: QualifiedInt<I, T, Q>, @Treapable Q: Qualifier<Q>, T: IntApprox<T>, S, W>(
    private val extractModularUpperBound: (Q) -> M?,
    private val extractMultipleOf: (Q) -> BigInteger?,
    private val modularUpperBound: (TACSymbol, BigInteger, Boolean) -> Q?,
    private val delegate: QualifierPropagationComputation<I, S, W, Q>
): QualifierPropagationComputation<I, S, W, Q>() {

    override fun propagateTrue(v: TACSymbol.Var, av: I, s: S, w: W, l: LTACCmd): Map<TACSymbol.Var, List<PathInformation<Q>>>? {
        val del = delegate.propagateTrue(v, av, s, w, l)
        val me = super.propagateTrue(v, av, s, w, l)
        return if (del != null && me != null) {
            me.pointwiseMerge(del) { v1, v2 -> v1 + v2 }
        } else {
            null
        }
    }

    override fun propagateFalse(v: TACSymbol.Var, av: I, s: S, w: W, l: LTACCmd): Map<TACSymbol.Var, List<PathInformation<Q>>>? {
        val del = delegate.propagateFalse(v, av, s, w, l)
        val me = super.propagateFalse(v, av, s, w, l)
        return if (del != null && me != null) {
            me.pointwiseMerge(del) { v1, v2 -> v1 + v2 }
        } else {
            null
        }
    }

    override fun extractValue(op1: TACSymbol.Var, s: S, w: W, l: LTACCmd): I? {
        return delegate.extractValue(op1, s, w, l)
    }

    override fun weakUpperBound(toRet: TACSymbol.Var, v: MutableList<PathInformation<Q>>, sym: TACSymbol.Var?, num: BigInteger?, s: S, w: W, l: LTACCmd) {
        // sym <= toRet && toRet <= sym ===> toRet == sym
        if (sym != null && extractValue(sym, s, w, l)?.qual?.any {q ->
                extractModularUpperBound(q)?.let {
                    it.other == toRet && !it.strong
                } == true
            } == true) {
            v.add(PathInformation.StrictEquality(sym = sym, num = null))
        }
    }

    override fun strictUpperBound(v: TACSymbol.Var, vQuals: MutableList<PathInformation<Q>>, sym: TACSymbol.Var?, num: BigInteger?, s: S, w: W, l: LTACCmd) {
        val target = extractValue(v, s, w, l) ?: return

        /* If we have that v < sym and ModularUpperBound(sym, m, false), then we can strengthen the bound
         * in the ModularUpperBound, setting its flag to true.
         */
         target.qual.mapNotNull(extractModularUpperBound).filter {
             (it.other == sym || (num != null && (it.other as? TACSymbol.Const)?.value == num)) && !it.strong
        }.mapNotNull {
            modularUpperBound(it.other, it.modulus, true)?.let{ PathInformation.Qual(it) }
        }.let(vQuals::addAll)

        /* If v = sym = 0 (mod f), then we have that ModularUppderBound(sym, f, true) for any f (since v < sym).
         * Find all known divisors of sym, and see if they are common with any known factors of v.
         */
        if (sym != null) {
            extractValue(sym, s, w, l)?.qual?.mapNotNull(extractMultipleOf)?.filter {
                target.isMultipleOf(it)
            }?.mapNotNull {
                modularUpperBound(sym, it, true)?.let { PathInformation.Qual(it) }
            }?.let(vQuals::addAll)
        }
    }

    override fun strictInequality(toRet: TACSymbol.Var, v: MutableList<PathInformation<Q>>, sym: TACSymbol.Var?, num: BigInteger?, s: S, w: W, l: LTACCmd) {
        // toRet != sym && toRet <= sym ===> toRet < sym
        if (sym != null) {
            if (extractValue(toRet, s, w, l)?.qual?.any { q ->
                extractModularUpperBound(q)?.let {
                    it.other == sym && !it.strong
                } == true
            } == true) {
                v.add(PathInformation.StrictUpperBound(sym = sym, num = null))
            }
        }

        // toRet != num && toRet <= num ===> toRet < num
        if (num != null) {
            if (extractValue(toRet, s, w, l)?.qual?.any { q ->
                    extractModularUpperBound(q)?.let {
                        (it.other as? TACSymbol.Const)?.value == num && !it.strong
                    } == true
                } == true) {
                v.add(PathInformation.StrictUpperBound(sym = null, num = num))
            }
        }

        // strengthen toRet's weak upper bound to strong, (since we know toRet != sym)
        extractValue(toRet, s, w, l)?.qual?.mapNotNull(extractModularUpperBound)?.filter {
            ((sym != null && it.other == sym) || (num != null && (it.other as? TACSymbol.Const)?.value == num)) && !it.strong
        }?.mapNotNull {
            modularUpperBound(it.other, it.modulus, true)?.let { PathInformation.Qual(it) }
        }?.let(v::addAll)

    }

    private fun I.isMultipleOf(isModulo: BigInteger): Boolean {
        return isModulo > BigInteger.ZERO
            && (isModulo == BigInteger.ONE
            || (x.isConstant && x.c.mod(isModulo) == BigInteger.ZERO)
            ||  qual.any { extractMultipleOf(it) == isModulo })
    }
}

fun <M: ModularUpperBoundQualifier, I: QualifiedInt<I, T, Q>, T: UIntApprox<T>, @Treapable Q: Qualifier<Q>, S, W>
    QualifierPropagationComputation<I, S, W, Q>.withModularUpperBounds(
    extractModularUpperBound: (Q) -> M?,
    extractMultipleOf: (Q) -> BigInteger?,
    modularUpperBound: (TACSymbol, BigInteger, Boolean) -> Q?,
) = ModularUpperBoundPropagator(
    extractModularUpperBound,
    extractMultipleOf,
    modularUpperBound,
    this
)
