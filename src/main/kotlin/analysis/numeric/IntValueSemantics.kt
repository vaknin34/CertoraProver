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

import analysis.LTACCmdView
import evm.MAX_EVM_UINT256
import vc.data.TACCmd
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * A [IValueSemantics] that operate over value abstractions of type [I] which contain some numeric abstraction of type [T]
 * (via the [WithUIntApproximation] interface)
 */
abstract class IntValueSemantics<I: WithIntApproximation<T>, T: IntApprox<T>, S, W> : AbstractValueSemantics<S, I, W>() {
    override fun evalShiftLeft(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S        ,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return v2.x.getLowerBound()?.let { lb ->
            if (lb >= UINT_BITWIDTH) {
                lift(BigInteger.ZERO)
            } else {
                v2.x.getUpperBound()?.let { ub ->
                    v1.x.shiftLeft(lb, ub)
                }
            }
        }?.let(this::lift) ?: nondet
    }

    override fun evalShiftRightLogical(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return v2.x.getLowerBound()?.let { lb ->
            if (lb >= UINT_BITWIDTH) {
                lift(BigInteger.ZERO)
            } else {
                v2.x.getUpperBound()?.let { ub ->
                    v1.x.shiftRight(lb, ub)
                }
            }
        }?.let(this::lift) ?: nondet
    }

    open fun lift(const: BigInteger): T = lift(const, const)

    /**
     * Lift a representation of the closed interval from [lb] to [ub] into
     * the numeric abstraction domain [T]
     */
    abstract fun lift(lb: BigInteger, ub: BigInteger) : T

    /**
     * Lift an numeric abstraction [T] into the full value domain [I]
     */
    abstract fun lift(iVal: T) : I

    protected fun I.isBit256Fragment() = this.x.getLowerBound()?.let { lb ->
        this.x.getUpperBound()?.let { ub ->
            BigInteger.ZERO <= lb && ub <= MAX_EVM_UINT256
        }
    } ?: false

    override fun evalBWAnd(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        if(!v1.isBit256Fragment() || !v2.isBit256Fragment()) {
            return nondet
        }
        if(v1.x.isConstant && v2.x.isConstant) {
            return lift(v1.x.c and v2.x.c).let(this::lift)
        }
        val ub1 = v1.x.ub
        val ub2 = v2.x.ub

        val minUb = ub1.min(ub2)
        /*
        (declare-const V1 (_ BitVec 256))
        (declare-const V2 (_ BitVec 256))
        (declare-const ub1 (_ BitVec 256))
        (declare-const ub2 (_ BitVec 256))

        (assert (bvule V1 ub1))

        (assert (bvule V2 ub2))

        (assert (not (bvule (bvand V1 V2) (ite (bvult ub1 ub2) ub1 ub2))))

        (check-sat)
        (get-model)

         */
        return lift(lb = BigInteger.ZERO, ub = minUb).let(this::lift)
    }

    private fun bitwiseOrWithConst(
        constOp: BigInteger, rangeOp: T
    ) : I? {
        /* The correctness of the following is given by the unsatisfiability of the following
        (declare-const ub (_ bv 256))
        (declare-const lb (_ bv 256))

        (declare-const gt (_ bv 256))

        (assert (bvult ub gt))
        (assert (bvule lb ub))

        (declare-const elem (_ bv 256))

        (assert (bvule elem ub))
        (assert (bvult lb elem))

        (define-const plus-ub (_ bv 256) (bvadd ub gt))
        (define-const plus-lb (_ bv 256) (bvadd lb gt))

        (define-fun is-mag ((op (_ bv 256)) (mag-val (_ bv 256))) Bool
          (or
           (and
            (= op (_ bv0 256))
            (= mag-val (_ bv0 256)))
           (and
            (bvult (_ bv0 256) mag-val)
            (= (bvlshr op mag-val) (_ bv0 256))
            (distinct (bvlshr op (bvsub mag-val (_ bv1 256))) (_ bv0 256)))))

        (declare-const ub-mag (_ bv 256))
        (assert (is-mag ub ub-mag))

        (define-const ub-mask (_ bv 256)
          (bvsub (bvshl (_ bv1 256) ub-mag) (_ bv1 256)))

        (assert (= (_ bv0 256)
                   (bvand ub-mask gt)))

        (define-const or (_ bv 256) (bvor gt elem))
        (assert (not
                 (and
                  (bvule plus-lb or)
                  (bvule or plus-ub))))

        (check-sat)
         */

        if(constOp == BigInteger.ZERO) {
            return lift(rangeOp)
        }
        check(constOp.lowestSetBit >= 0)
        /*
         * The lowest set bit check is equivalent to the lower-bound mask above via the following:
         * (define-fun is-mag ((op (_ bv 256)) (mag-val (_ bv 256))) Bool
              (or
               (and
                (= op (_ bv0 256))
                (= mag-val (_ bv0 256)))
               (and
                (bvult (_ bv0 256) mag-val)
                (= (bvlshr op mag-val) (_ bv0 256))
                (distinct (bvlshr op (bvsub mag-val (_ bv1 256))) (_ bv0 256)))))

            (define-fun lowest-set-bit ((op (_ bv 256)) (lowest (_ bv 256))) Bool
              (or (= op (_ bv0 256))
                  (and
                   (= (bvshl (bvlshr op lowest) lowest)
                      op)
                   (let ((nxt (bvadd lowest (_ bv1 256))))
                     (distinct (bvshl (bvlshr op nxt) nxt) op)))))

            (declare-const ub (_ bv 256))
            (declare-const gt (_ bv 256))
            (declare-const mag (_ bv 256))
            (declare-const lowest (_ bv 256))

            (assert (is-mag ub mag))
            (assert (lowest-set-bit gt lowest))

            (define-const lower-mask (_ bv 256)
              (bvsub (bvshl (_ bv1 256) mag) (_ bv1 256)))

            (assert (= (bvand gt lower-mask) (_ bv0 256)))
            (assert (bvult (_ bv0 256) gt))

            (assert (not
                     (bvule mag lowest)))

            (check-sat)
         */
        val ub = rangeOp.ub
        val lb = rangeOp.lb
        if(constOp.lowestSetBit >= ub.bitLength()) {
            return lift(lift(lb = lb + constOp, ub + constOp))
        }
        return null
    }

    override fun evalBWOr(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        if(!v1.isBit256Fragment() || !v2.isBit256Fragment()) {
            return nondet
        }
        if(v1.x.isConstant) {
            val constOp = v1.x.c
            if(v2.x.isConstant) {
                return lift(lift(constOp or v2.x.c))
            }
            bitwiseOrWithConst(constOp, rangeOp = v2.x)?.let { return it }
        } else if(v2.x.isConstant) {
            bitwiseOrWithConst(v2.x.c, v1.x)?.let { return it }
        }
        /*
           Safety of these !! established by the isBit256 fragment
         */
        return v1.x.ub.let { ub1 ->
            v2.x.ub.let { ub2 ->
                BigInteger.TWO.pow(ub1.max(ub2).bitLength()) - BigInteger.ONE
            }
        }.let { newUb ->
            /*
            (declare-const a (_ BitVec 256))
            (declare-const b (_ BitVec 256))

            (declare-const d (_ BitVec 256))
            (declare-const c (_ BitVec 256))

            (assert (bvule a c))
            (assert (bvule b d))

            (assert (not
                 (bvule
                  (ite (bvult a b) a b)
                  (bvor c d))))

            (check-sat)
             */
            val newLb = v1.x.lb.max(v2.x.lb)
            lift(lb = newLb, ub = newUb)
        }.let(this::lift)
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
        return lift(lift(BigInteger.ZERO, BigInteger.ONE))
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
        return lift(lift(BigInteger.ZERO, BigInteger.ONE))
    }

    override fun evalLe(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        val mustBeLe = v1.x.getUpperBound()?.let { v1Ub ->
            v2.x.getLowerBound()?.let { v2Lb ->
                v1Ub <= v2Lb
            }
        } == true
        val mustNotBeLe = v1.x.getLowerBound()?.let { v1Lb ->
            v2.x.getUpperBound()?.let { v2Ub ->
                v1Lb > v2Ub
            }
        } == true
        return (if(mustBeLe) {
            lift(BigInteger.ONE)
        } else if(mustNotBeLe) {
            lift(BigInteger.ZERO)
        } else {
            lift(lb = BigInteger.ZERO, ub = BigInteger.ONE)
        }).let(this::lift)
    }

    override fun evalLt(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        val mustBeLt = v1.x.getUpperBound()?.let { i1 ->
            v2.x.getLowerBound()?.let { i2 ->
                (i1 < i2)
            }
        } == true
        val mustNotBeLt = v1.x.getLowerBound()?.let { i1 ->
            v2.x.getUpperBound()?.let { i2 ->
                i1 >= i2
            }
        } == true
        return (if (mustBeLt) {
            lift(BigInteger.ONE)
        } else if (mustNotBeLt) {
            lift(BigInteger.ZERO)
        } else {
            lift(lb = BigInteger.ZERO, ub = BigInteger.ONE)
        }).let(this::lift)
    }

    private val signedIntCutOff = BigInteger("8000000000000000000000000000000000000000000000000000000000000000", 16)

    private val T.ub get() = this.getUpperBound()!!
    private val T.lb get() = this.getLowerBound()!!

    private fun isSlt(v1: T, v2: T) : Boolean =
        /* v1 is negative (it must be greater than or equal to 2^255) and v2 is positive (it is strictly LESS than 2^255) */
        (v1.lb >= signedIntCutOff && v2.ub < signedIntCutOff) ||
                // the same sign
                (isSameSign(v1, v2) &&
                        /* AND v1 is provably smaller than v2 */
                        v1.ub < v2.lb)

    /**
    inverse of the above, but note that !isSlt does not necessarily imply that isNotSlt (because we could not know)
     */
    private fun isNotSlt(v1: T, v2: T) : Boolean =
        /* v1 is definitely positive and v2 is definitely negative */
        (v1.ub < signedIntCutOff && v2.lb >= signedIntCutOff) ||
                /* or, either both are "positive" or both are negative */
                (isSameSign(v1, v2) &&
                        /* AND v1 is provably LARGER than v2 */
                        v1.lb > v2.ub)

    private fun isSameSign(v1: T, v2: T) =
        /* both are positive, i.e., less than 2^255 */
        (v1.ub < signedIntCutOff && v2.ub < signedIntCutOff) ||
                /* or both are negative, i.e. greater or equal to 2^255, ... */
                (v1.lb >= signedIntCutOff && v2.lb >= signedIntCutOff)

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
        // doing a signed LT check doesn't *really* make sense for open ranges
        if(!v1.isBit256Fragment() || !v2.isBit256Fragment()) {
            return lift(lift(BigInteger.ZERO, BigInteger.ONE))
        }
        return lift(if(isSlt(v1.x, v2.x)) {
            lift(BigInteger.ONE)
        } else if(isNotSlt(v1.x, v2.x)) {
            lift(BigInteger.ZERO)
        } else {
            lift(BigInteger.ZERO, BigInteger.ONE)
        })
    }

    override fun evalEq(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        val staticCompResult = if (o1 == o2) {
            lift(BigInteger.ONE)
        } else if (v1.x.getLowerBound()?.let { v1Lb ->
                v2.x.getUpperBound()?.let { v2Ub ->
                    v1Lb > v2Ub
                }
            } == true ||
            v1.x.getUpperBound()?.let { v1Ub ->
                v2.x.getLowerBound()?.let { v2Lb ->
                    v2Lb > v1Ub
                }
            } == true
        ) {
            lift(BigInteger.ZERO)
        } else if (v1.x.isConstant && v2.x.isConstant) {
            lift(
                if (v1.x.c == v2.x.c) {
                    BigInteger.ONE
                } else {
                    BigInteger.ZERO
                }
            )
        } else {
            lift(lb = BigInteger.ZERO, ub = BigInteger.ONE)
        }
        return lift(staticCompResult)
    }

    override fun evalSub(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        val (res, _) = v1.x.sub(v2.x)
        return this.lift(res)
    }

    override fun evalAdd(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        val (newIntVal, _) = v1.x.add(v2.x)
        return this.lift(newIntVal)
    }

    override fun evalAddMod(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, v3: I, o3: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        val (newIntVal, overflow) = v1.x.add(v2.x)

        return if (!overflow && newIntVal.getUpperBound()?.let { it < (v3.x.getLowerBound() ?: BigInteger.ZERO) } == true) {
            this.evalAdd(v1, o1, v2, o2, toStep, input, whole, l)
        } else {
            // v3 better not be 0
            val max = v3.x.getUpperBound()?.takeIf { it > BigInteger.ZERO }?.subtract(BigInteger.ONE)
            val numAbs = this.lift(BigInteger.ZERO, max ?: MAX_EVM_UINT256)
            this.lift(numAbs)
        }
    }

    override fun evalMult(v1: I, o1: TACSymbol, v2: I, o2: TACSymbol, toStep: S, input: S, whole: W, l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>): I {
        val (res, _) = v1.x.mult(v2.x)
        return lift(res)
    }

    override fun evalLNot(
        v1: I,
        s: TACSymbol,
        toStep: S,
        input: S,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return lift(lift(BigInteger.ZERO, BigInteger.ONE))
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
        return if(i.x.isConstant && i.x.c == BigInteger.ZERO) {
            e
        } else if(!i.x.mayEqual(BigInteger.ZERO)) {
            t
        } else {
            lift(t.x.join(e.x))
        }
    }

    override fun evalSignExtend(
        v1: I,
        o1: TACSymbol,
        v2: I,
        o2: TACSymbol,
        toStep: S,
        input: S        ,
        whole: W,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): I {
        return if (v2.x.isConstant && v2.x.c == BigInteger.ZERO) {
            v2
        } else {
            nondet
        }
    }
}
