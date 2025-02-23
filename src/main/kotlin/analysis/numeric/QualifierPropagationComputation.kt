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
import evm.MAX_EVM_INT256
import evm.MAX_EVM_UINT256
import evm.MIN_EVM_INT256_2S_COMPLEMENT
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * A base implementation of logic for collecting [PathInformation] induced by propagating
 * true or false path conditions. Client analyses may apply this path information themselves,
 * or have it done automatically with implementations of [QualifiedIntPropagationSemantics]
 *
 * [I] is a [QualifiedInt] that is the abstraction of variables in state [S]; these states may
 * be embedded within larger states of type [W].
 */
abstract class QualifierPropagationComputation<I: QualifiedInt<*, *, *>, in S, in W, Q> {
    /*
       An implementation note about how we handle signed less than/less than or equals.

       x SLT y is encoded as:
       (x >= 0x8.... && y < 0x8.....) || (x < 0x8.... = y < 0x8....... && x < y)
       i.e. x is greater than the SIGNED uint max (and y is not), i.e., x is "negative" and y is not,
       OR they have the same sign (the equality in the second disjunct) and x < y is unsigned comparison.

       if we know that x SLT y is true, then we must have that either:
       a) x >= 0x8.... and y < 0x8..... OR
       b) x < y

       So in propagateTrue slt we check if we can prove that x MUST be LESS than 0x8.... in which case only b may be true.

       Proof:
       (declare-const A Int)
        (declare-const B Int)
        (declare-const CUT Int)
        (assert (<= 0 A))
        (assert (<= 0 B))
        (assert (<= 0 CUT))

        (assert (or
                 (and
                  (>= A CUT) (< B CUT))
                 (and
                  (= (< A CUT) (< B CUT))
                  (< A B))))
        (assert (< A CUT))

        (assert (not (< A B)))
        (check-sat)


       Now consider the false case, i.e. !(x SLT y), AKA:
       (x < 0x8.... \/ y >= 0x8....) /\ (x < 0x8.... != y < 0x8..... \/ x >= y)

       Fun fact: this is in fact just y SLE x as we would hope. So the false case requires no additional handling
       beyond "flipping" the conditional and swapping operands; the implementation of propagateSle/slt will check
       the first operand as necessary.
     */
    /**
     * Propagate that the value of [v] (given by [av]) is true (i.e., non-zero) along a path to [l].
     *
     * Returns a map of variables to the path information to propagate to those variables; a return value
     * of null indicates that the path is infeasible.
     */
    open fun propagateTrue(v: TACSymbol.Var, av: I, s: S, w: W, l: LTACCmd): Map<TACSymbol.Var, List<PathInformation<Q>>>? {
        val c : IntApprox<*> = av.x
        if(c.mustEqual(BigInteger.ZERO)) {
            return null
        }
        val toPropagate = mutableMapOf<TACSymbol.Var, MutableList<PathInformation<Q>>>()
        for(q in av.qual) {
            if(!this.propagateTrueQualifier(toPropagate, q, s, w, l, av, v)) {
                return null
            }
        }
        return toPropagate
    }

    /**
     * Collect path information (stored in [out]) when the qualifier [q] appears in the value that must be non-zero.
     *
     * [av] is the condition value in which [q] appears, and [cond] is the condition variable.
     *
     * Returning false indicates that the path being processed is actually infeasible.
     */
    protected open fun propagateTrueQualifier(
        out: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        q: Qualifier<*>,
        s: S,
        w: W,
        l: LTACCmd,
        av: I,
        cond: TACSymbol.Var
    ): Boolean {
        when(q) {
            is ConditionQualifier -> {
                if(!propagateCondition(q.op1, q.op2, q.condition, out, s, w, l)) {
                    return false
                }
            }
            is LogicalConnectiveQualifier -> {
                if(q.connective == LogicalConnectiveQualifier.LBinOp.AND) {
                    if(!recursivePropagation(q.op1, q.applyNot, out, s, w, l)) {
                        return false
                    }
                    if(!recursivePropagation(q.op2, q.applyNot, out, s, w, l)) {
                        return false
                    }
                }
            }
        }
        return true
    }

    private fun propagateCondition(op1: TACSymbol, op2: TACSymbol, condition: ConditionQualifier.Condition, toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>, s: S, w: W, l: LTACCmd): Boolean {
        return when(condition) {
            ConditionQualifier.Condition.EQ -> {
                propagateEq(op1, op2, toRet, s, w, l)
            }
            ConditionQualifier.Condition.NEQ -> propagateNe(op1, op2, toRet, s, w, l)
            ConditionQualifier.Condition.LT -> propagateLt(op1, op2, toRet, s, w, l)
            ConditionQualifier.Condition.LE -> propagateLe(op1, op2, toRet, s, w, l)
            ConditionQualifier.Condition.SLT -> propagateSlt(op1, op2, toRet, s, w, l)
            ConditionQualifier.Condition.SLE -> propagateSle(op1, op2, toRet, s, w, l)
        }
    }



    /**
      Check whether the argument (assumed to be the first operand of an SLT/SLE) is less than [MAX_EVM_INT256],
      i.e. it is positive.
     */
    private fun definitelyPositive(sym: TACSymbol, s: S, w: W, l: LTACCmd) =
        when(sym) {
            is TACSymbol.Const -> sym.value <= MAX_EVM_INT256
            is TACSymbol.Var -> extractValue(sym, s, w, l)?.x?.let { q: IntApprox<*> ->
                q.getLowerBound()?.let {
                    it >= BigInteger.ZERO
                } == true && q.getUpperBound()?.let {
                    it <= MAX_EVM_INT256
                } == true
            } ?: false
        }

    private fun definitelyNegative(sym: TACSymbol, s: S, w: W, l: LTACCmd) =
        when(sym) {
            is TACSymbol.Const -> sym.value >= MIN_EVM_INT256_2S_COMPLEMENT
            is TACSymbol.Var -> extractValue(sym, s, w, l)?.x?.let { q: IntApprox<*> ->
                q.getUpperBound()?.let {
                    it <= MAX_EVM_UINT256
                } == true &&
                q.getLowerBound()?.let {
                    it >= MIN_EVM_INT256_2S_COMPLEMENT
                } == true
            } ?: false
        }

    protected open fun propagateSle(op1: TACSymbol, op2: TACSymbol, toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>, s: S, w: W, l: LTACCmd): Boolean {
        /*
            if op1 is (provably) positive, then:
            1. op2 must be bounded below by the value of op1, and
            2. op2 must be bounded above by the max signed int value
         */
        if(definitelyPositive(op1, s, w, l)) {
            propagateLe(op1, op2, toRet, s, w, l)
            propagateDefinitelyPositive(op2, toRet, l, s, w)
        }
        /*
          if op2 is (provably) negative, then:
          1. op1 is bounded above by the (unsigned) value of op2
          2. op1 is bounded below by MAX_INT_256 + 1 (aka, MIN_EVM_INT256)
         */
        if(definitelyNegative(op2, s, w, l)) {
            propagateLe(op1, op2, toRet, s, w, l)
            propagateDefinitelyNegative(op1, toRet, s, w, l)
        }
        if(op1 is TACSymbol.Var && op2 is TACSymbol.Var) {
            addPathInformation(toRet, op1) { q ->
                q.add(PathInformation.WeakSignedUpperBound(op2))
            }
            addPathInformation(toRet, op2) { q ->
                q.add(PathInformation.WeakSignedLowerBound(op1))
            }
        }
        return true
    }

    /**
     * Propagate that [op1] is signed less than [op2] in state [s] embedded in larger state [w]. Computed path information
     * is propagated into [toRet]. Returns false if this case is not possible (i.e., op1 cannot be slt op2)
     */
    protected open fun propagateSlt(op1: TACSymbol, op2: TACSymbol, toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>, s: S, w: W, l: LTACCmd): Boolean {
        if(definitelyPositive(op1,  s, w, l)) {
            propagateLt(op1, op2, toRet, s, w, l)
            propagateDefinitelyPositive(
                op2, toRet, l, s, w
            )
        }
        val op2IsNeg = definitelyNegative(op2, s, w, l)
        if(op2IsNeg) {
            propagateLt(op1, op2, toRet, s, w, l)
        }
        if(op2IsNeg || (op2 is TACSymbol.Var && extractExactValue(op2, s, w, l) == BigInteger.ZERO) || (op2 is TACSymbol.Const && op2.value == BigInteger.ZERO)) {
            propagateDefinitelyNegative(
                op1, toRet, s, w, l
            )
        }
        if(op2 is TACSymbol.Var && op1 is TACSymbol.Var) {
            addPathInformation(toRet, op1) { q ->
                q.add(PathInformation.StrictSignedUpperBound(op2))
            }
            addPathInformation(toRet, op2) { q ->
                q.add(PathInformation.StrictSignedLowerBound(op1))
            }
        }
        return true
    }

    private fun propagateDefinitelyNegative(
        op1: TACSymbol,
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        s: S,
        w: W,
        l: LTACCmd
    ) {
        if (op1 is TACSymbol.Var) {
            weakLowerBound(
                toRet = toRet,
                v = op1,
                s = s,
                w = w,
                l = l,
                sym = null,
                num = MIN_EVM_INT256_2S_COMPLEMENT
            )
        }
    }

    private fun propagateDefinitelyPositive(
        op2: TACSymbol,
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        l: LTACCmd,
        s: S,
        w: W
    ) {
        if (op2 is TACSymbol.Var) {
            weakUpperBound(
                toRet = toRet,
                v = op2,
                l = l,
                s = s,
                w = w,
                num = MAX_EVM_INT256,
                sym = null
            )
        }
    }


    /**
     * Propagate that [op1] must not be equal to [op2], storing this information into [toRet].
     *
     * Returning false indicates that this path is actually infeasible.
     */
    protected open fun propagateNe(
        op1: TACSymbol,
        op2: TACSymbol,
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        s: S,
        w: W,
        l: LTACCmd
    ): Boolean {
        if(op1 is TACSymbol.Var) {
            if(op2 is TACSymbol.Const) {
                this.tightenEndPointsNE(op1, op2, s, w, l, toRet)
            }
            qualifierAdd(
                num = extractExactSymValue(op2, s, w, l),
                w = w,
                s = s,
                where = l,
                sym = op2 as? TACSymbol.Var,
                mk = PathInformation.Companion::StrictInequality,
                tgt = op1,
                toRet = toRet,
                userCallback = this::strictInequality
            )
        }
        if(op2 is TACSymbol.Var) {
            if(op1 is TACSymbol.Const) {
                this.tightenEndPointsNE(op2, op1, s, w, l, toRet)
            }
            qualifierAdd(
                num = extractExactSymValue(op1, s, w, l),
                userCallback = this::strictInequality,
                toRet = toRet,
                tgt = op2,
                sym = op1 as? TACSymbol.Var,
                mk = PathInformation.Companion::StrictInequality,
                where = l,
                s = s,
                w = w
            )
        }
        return true
    }

    open protected fun strictInequality(
        toRet: TACSymbol.Var,
        v: MutableList<PathInformation<Q>>,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        l: LTACCmd
    ) { }

    private fun tightenEndPointsNE(
            op1: TACSymbol.Var,
            op2: TACSymbol.Const,
            s: S,
            w: W,
            l: LTACCmd,
            toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>
    ) {
        val i : IntApprox<*> = this.extractValue(op1, s, w, l)?.x ?: return
        if(i.getUpperBound() == op2.value) {
            strictUpperBound(toRet, op1, sym = null, num = op2.value, s, w, l)
        }
        if(i.getLowerBound() == op2.value) {
            strictLowerBound(toRet, op1, sym = null, num = op2.value, s, w, l)
        }
    }

    /**
     * Extract the value of [op1] as an element of [I] from the state [s]. null
     * indicates that there is no meaningful or non-trivial valuation possible for [op1]
     */
    abstract fun extractValue(op1: TACSymbol.Var, s: S, w: W, l: LTACCmd): I?

    /**
     * Propagate that [op1] must  be less that or equal [op2], storing this information into [toRet].
     *
     * Returning false indicates that this path is actually infeasible.
     */
    protected open fun propagateLe(
        op1: TACSymbol,
        op2: TACSymbol,
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        s: S,
        w: W,
        l: LTACCmd
    ): Boolean {
        when {
            op1 is TACSymbol.Var && op2 is TACSymbol.Var -> {
                weakUpperBound(toRet, op1, sym = op2, num = extractUpperBound(op2, s, w, l), s, w, l)
                weakLowerBound(toRet, op2, sym = op1, num = extractLowerBound(op1, s, w, l), s, w, l)
            }
            op1 is TACSymbol.Var && op2 is TACSymbol.Const -> {
                weakUpperBound(toRet, op1, sym = null, num = op2.value, s, w, l)
            }
            op1 is TACSymbol.Const && op2 is TACSymbol.Var -> {
                weakLowerBound(toRet, op2, sym = null, num = op1.value, s, w, l)
            }
        }
        return true
    }

    /**
     * Propagate that [op1] must be equal to [op2], storing this information into [toRet].
     *
     * Returning false indicates that this path is actually infeasible.
     */
    protected open fun propagateEq(
        op1: TACSymbol,
        op2: TACSymbol,
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        s: S,
        w: W,
        l: LTACCmd
    ): Boolean {
        when {
            op1 is TACSymbol.Var && op2 is TACSymbol.Var -> {
                strictEquality(
                    toRet = toRet,
                    v = op1,
                    sym = op2,
                    num = extractExactValue(op2, s, w, l), s, w, l
                )
                strictEquality(
                    toRet = toRet,
                    v =  op2,
                    sym = op1,
                    num = extractExactValue(op1, s, w, l), s, w, l
                )
            }
            op1 is TACSymbol.Var && op2 is TACSymbol.Const -> {
                strictEquality(toRet, op1, sym = null, num = op2.value, s, w, l)
            }
            op1 is TACSymbol.Const && op2 is TACSymbol.Var -> {
                strictEquality(toRet, op2, sym = null, num = op1.value, s, w, l)
            }
        }
        return true
    }

    protected fun extractExactSymValue(op: TACSymbol, s: S, w: W, l: LTACCmd) : BigInteger? = when(op) {
        is TACSymbol.Const -> op.value
        is TACSymbol.Var -> {
            val v : TACSymbol.Var = op
            extractExactValue(v, s, w, l)
        }
    }

    protected open fun extractExactValue(op: TACSymbol.Var, s: S, w: W, l: LTACCmd) : BigInteger? =
            extractValue(op,  s, w, l)?.x?.takeIf { it: IntApprox<*> -> it.isConstant }?.let { it: IntApprox<*> ->
                it.c
            }

    protected open fun extractLowerBound(op: TACSymbol.Var, s: S, w: W, l: LTACCmd) : BigInteger? =
        extractValue(op, s, w, l)?.x?.let { it: IntApprox<*> -> it }?.getLowerBound()

    protected open fun extractUpperBound(op: TACSymbol.Var, s: S, w: W, l: LTACCmd) : BigInteger? =
        extractValue(op, s, w, l)?.x?.let { it: IntApprox<*> -> it }?.getUpperBound()

    /**
     * Add the path information via [cb] to the constraints collected for [tgt] in [toRet]
     */
    protected fun addPathInformation(toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>, tgt: TACSymbol.Var, cb: (MutableList<PathInformation<Q>>) -> Unit) {
        cb(toRet.computeIfAbsent(tgt) { mutableListOf() })
    }

    private fun qualifierAdd(
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        tgt: TACSymbol.Var,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        where: LTACCmd,
        userCallback: (TACSymbol.Var, MutableList<PathInformation<Q>>, TACSymbol.Var?, BigInteger?, S, W, LTACCmd) -> Unit,
        mk: (TACSymbol.Var?, BigInteger?) -> PathInformation<Q>,
    ) {
        addPathInformation(toRet, tgt) {
            userCallback(tgt, it, sym, num, s, w, where)
            it.add(mk(sym, num))
        }
    }

    /**
     * Hook called when it is inferred that [v] is has a strict upper bound in [sym] and [num].
     * The path information for [v] is stored in [vQuals] and may be mutated by implementers.
     *
     * Context arguments ([s], [w] and [l] have their usual interpretation)
     */
    protected open fun strictUpperBound(
        v: TACSymbol.Var,
        vQuals: MutableList<PathInformation<Q>>,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        l: LTACCmd
    ) { }

    private fun strictUpperBound(
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        v: TACSymbol.Var,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        l: LTACCmd
    ) {
        qualifierAdd(toRet, v, sym, num, s, w, l, this::strictUpperBound, PathInformation.Companion::StrictUpperBound)
    }

    /**
     * Hook called with [toRet] is known to have some strict lower bound in [sym] or [num].
     * The path information for [toRet] is stored in [v] and may be safely mutated by implementers.
     * Context arguments [s], [w], and [l] are as usual
     */
    protected open fun strictLowerBound(
        toRet: TACSymbol.Var,
        v: MutableList<PathInformation<Q>>,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        l: LTACCmd
    ) { }

    private fun strictLowerBound(
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        v: TACSymbol.Var,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        l: LTACCmd
    ) {
        qualifierAdd(toRet, v, sym, num, s, w, l, this::strictLowerBound, PathInformation.Companion::StrictLowerBound)
    }

    protected open fun weakLowerBound(
        toRet: TACSymbol.Var,
        v: MutableList<PathInformation<Q>>,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        l: LTACCmd
    ) { }

    private fun weakLowerBound(
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        v: TACSymbol.Var,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        l: LTACCmd
    ) {
        qualifierAdd(toRet, v, sym, num, s, w, l, this::weakLowerBound, PathInformation.Companion::WeakLowerBound)
    }

    /**
     * Called when it is shown that [toRet] has a weak upper bound in [sym] and [num].
     * [v] stores the path information for [toRet] and may be safely mutated by callers.
     * context arguments [s], [w], [l] have their usual interpretation.
     */
    protected open fun weakUpperBound(
        toRet: TACSymbol.Var,
        v: MutableList<PathInformation<Q>>,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        l: LTACCmd
    ) { }

    private fun weakUpperBound(
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        v: TACSymbol.Var,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        l: LTACCmd
    ) {
        qualifierAdd(toRet, v, sym, num, s, w, l, this::weakUpperBound, PathInformation.Companion::WeakUpperBound)
    }

    /**
     * Called when [toRet] is known to be strictly equal to [sym] and/or [num].
     * [v] holds the path information for [toRet] and may be safely mutated by implementers.
     * context arguments [s], [w], [l] have their usual interpretation.
     */
    protected open fun strictEquality(
        toRet: TACSymbol.Var,
        v: MutableList<PathInformation<Q>>,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        l: LTACCmd
    ) { }

    private fun strictEquality(
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        v: TACSymbol.Var,
        sym: TACSymbol.Var?,
        num: BigInteger?,
        s: S,
        w: W,
        l: LTACCmd
    ) {
        qualifierAdd(toRet, v, sym, num, s, w, l, this::strictEquality, PathInformation.Companion::StrictEquality)
    }

    /**
     * Propagate that [op1] must be less than [op2], storing this information into [toRet].
     *
     * Returning false indicates that this path is actually infeasible.
     */
    protected open fun propagateLt(
        op1: TACSymbol,
        op2: TACSymbol,
        toRet: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        s: S,
        w: W,
        l: LTACCmd
    ) : Boolean {
        when {
            op1 is TACSymbol.Var && op2 is TACSymbol.Var -> {
                strictUpperBound(toRet, op1, sym = op2, num = extractUpperBound(op2, s, w, l), s, w, l)
                strictLowerBound(toRet, op2, sym = op1, num = extractLowerBound(op1, s, w, l), s, w, l)
            }
            op1 is TACSymbol.Var && op2 is TACSymbol.Const -> {
                strictUpperBound(toRet, op1, sym = null, num = op2.value, s, w, l)
            }
            op1 is TACSymbol.Const && op2 is TACSymbol.Var -> {
                strictLowerBound(toRet, op2, sym = null, num = op1.value, s, w, l)
            }
        }
        return true
    }

    /**
     * Collect path information (stored in [out]) when the qualifier [q] appears in the value that must be zero (i.e., false).
     *
     * [av] is the condition value in which [q] appears, and [cond] is the condition variable.
     *
     * Returning false indicates that the path being processed is actually infeasible.
     */
    protected open fun propagateFalseQualifier(
            out: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
            q: Qualifier<*>,
            s: S,
            w: W,
            l: LTACCmd,
            av: I,
            v: TACSymbol.Var
    ): Boolean {
        when(q) {
            is ConditionQualifier -> {
                if(!propagateCondition(q.op2, q.op1, q.condition.flip(), out, s, w, l)) {
                    return false
                }
            }
            is LogicalConnectiveQualifier -> {
                if(q.connective.flip() == LogicalConnectiveQualifier.LBinOp.AND) {
                    if (!recursivePropagation(q.op1, !q.applyNot, out, s, w, l)) {
                        return false
                    }
                    if(!recursivePropagation(q.op2, !q.applyNot, out, s, w, l)) {
                        return false
                    }
                }
            }
        }
        return true
    }

    private fun recursivePropagation(
        op: TACSymbol.Var,
        applyNot: Boolean,
        out: MutableMap<TACSymbol.Var, MutableList<PathInformation<Q>>>,
        s: S,
        w: W,
        l: LTACCmd
    ): Boolean {
        val applyCond = { o1: TACSymbol, o2: TACSymbol, c: ConditionQualifier.Condition ->
            if(applyNot) {
                propagateCondition(o2, o1, condition = c.flip(), out,  s, w, l)
            } else {
                propagateCondition(o1, o2, c, out, s, w, l)
            }
        }
        extractValue(op, s, w, l)?.qual?.forEach {
            if(it is ConditionQualifier) {
                if(!applyCond(it.op1, it.op2, it.condition)) {
                    return false
                }
            } else if(it is LogicalConnectiveQualifier &&
                ((applyNot && it.connective == LogicalConnectiveQualifier.LBinOp.OR) ||
                        (!applyNot && it.connective == LogicalConnectiveQualifier.LBinOp.AND))){
                if(!recursivePropagation(
                    it.op1,
                    applyNot = applyNot.xor(it.applyNot),
                    out = out, s = s, w = w, l = l
                )) {
                    return false
                }
                if(!recursivePropagation(
                        it.op2,
                        applyNot = applyNot.xor(it.applyNot),
                        out = out,s = s, w = w, l = l
                )) {
                    return false
                }
            }
        }
        return true
    }

    /**
     * Propagate that the value of [v] (given by [av]) is true (i.e., non-zero) along a path to [l].
     *
     * Returns a map of variables to the path information to propagate to those variables; a return value
     * of null indicates that the path is infeasible.
     */
    open fun propagateFalse(v: TACSymbol.Var, av: I, s: S, w: W, l: LTACCmd): Map<TACSymbol.Var, List<PathInformation<Q>>>? {
        val c : IntApprox<*> = av.x
        if(!c.mayEqual(BigInteger.ZERO)) {
            return null
        }
        val toPropagate = mutableMapOf<TACSymbol.Var, MutableList<PathInformation<Q>>>()
        for(q in av.qual) {
            if(!this.propagateFalseQualifier(toPropagate, q, s, w, l, av, v)) {
                return null
            }
        }
        return toPropagate
    }
}
