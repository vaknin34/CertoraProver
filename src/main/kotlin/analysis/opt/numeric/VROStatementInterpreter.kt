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
import analysis.LTACCmdView
import analysis.numeric.AbstractStatementInterpreter
import analysis.numeric.IExpressionInterpreter
import analysis.numeric.OpenInterval
import analysis.numeric.QualifiedIntPropagationSemantics
import analysis.opt.intervals.Interval
import com.certora.collect.*
import datastructures.stdcollections.*
import evm.EVM_BITWIDTH256
import evm.EVM_BYTE_SIZE
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * A statement interpreter for states [S] that is a map from variables to [VROInt],
 * which uses the [expSemantics] and [pathSemantics]. [vc.data.TACCmd.Simple.AssigningCmd.AssignExpCmd]
 * delegate to [expSemantics] per usual, but with short-circuiting to prevent stepping if boolean operations are not
 * in the TAC fragment (why this was important is now lost to time), and with special handling of the
 * [vc.data.TACExpr.BinOp.SignExtend] expression which can't be handled in the expresison semantics for
 * reasons lost to time (they probably could, but no one bothered to move it).
 *
 * In addition, this class interprets [vc.data.TACCmd.Simple.Assume] and [vc.data.TACCmd.Simple.AssumeNotCmd] commands,
 * updating the state according to the [pathSemantics]. There are additional "hooks" in the form of [stepAssumeFalse]
 * and [stepAssumeTrue] which allow overriders to take extra actions on assume/assumenot; this used in the safe math
 * code to generate safe math proofs from what cannot be true.
 */
abstract class VROStatementInterpreter<S: Map<TACSymbol.Var, VROInt>>(
    private val expSemantics: IExpressionInterpreter<S, Any>,
    private val pathSemantics: QualifiedIntPropagationSemantics<VROInt, S, Any, VROQuals>
) : AbstractStatementInterpreter<S, Any>() {

    companion object {
        fun getExtendedBitIndex(c: BigInteger): Int? {
            val evmIdx = EVM_BITWIDTH256.toBigInteger() - (EVM_BYTE_SIZE * (c + BigInteger.ONE))
            if (evmIdx <= BigInteger.ZERO) {
                return null
            }
            return ((EVM_BITWIDTH256.toBigInteger() - evmIdx) - BigInteger.ONE).toInt()
        }
    }

    /**
     * Called when stepping an [vc.data.TACCmd.Simple.AssumeNotCmd] with operand [conditionVar],
     * that is the condition in [conditionVar] (with abstract value [conditionVal]) must be *true*.
     * [input] is the state at the beginning of the command,
     * [stepped] is the state *after* applying [pathSemantics]'s [QualifiedIntPropagationSemantics.propagateTrue]
     * on the [conditionVal].
     */
    protected open fun stepAssumeTrue(
        stepped: S,
        conditionVal: VROInt,
        conditionVar: TACSymbol.Var,
        input: S,
        l: LTACCmd
    ) : S {
        return stepped
    }

    /**
     * Called when stepping an [vc.data.TACCmd.Simple.AssumeNotCmd] with operand [conditionVar],
     * that is the condition in [conditionVar] (with abstract value [conditionVal]) must be *false*.
     * [input] is the state at the beginning of the command,
     * [stepped] is the state *after* applying [pathSemantics]'s [QualifiedIntPropagationSemantics.propagateFalse]
     * with the [conditionVal].
     */
    protected open fun stepAssumeFalse(
        stepped: S,
        conditionVal: VROInt,
        conditionVar: TACSymbol.Var,
        input: S,
        l: LTACCmd
    ) : S {
        return stepped
    }

    override fun stepCommand(l: LTACCmd, toStep: S, input: S, whole: Any): S {
        if (l.cmd is TACCmd.Simple.AssumeCmd) {
            if(l.cmd.cond !is TACSymbol.Var) {
                return super.stepCommand(l, toStep, input, whole)
            }
            val stepped = pathSemantics.propagateTrue(
                v = l.cmd.cond,
                s = toStep,
                w = toStep,
                l = l
            ) ?: return super.stepCommand(l, toStep, input, whole)
            return stepAssumeTrue(
                stepped,
                input = toStep,
                l = l,
                conditionVal = toStep[l.cmd.cond] ?: return stepped,
                conditionVar = l.cmd.cond
            )
        } else if(l.cmd is TACCmd.Simple.AssumeNotCmd) {
            if (l.cmd.cond !is TACSymbol.Var || l.cmd.cond !in toStep) {
                return super.stepCommand(l, toStep, input, whole)
            }
            val a = toStep[l.cmd.cond]!!
            val stepped = pathSemantics.propagateFalse(
                v = l.cmd.cond,
                s = toStep,
                w = toStep,
                l = l
            ) ?: return super.stepCommand(l, toStep, input, whole)
            return stepAssumeFalse(
                input = toStep,
                conditionVar = l.cmd.cond,
                l = l,
                stepped = stepped,
                conditionVal = a
            )
        } else if(l.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && l.cmd.rhs is TACExpr.BinBoolOp && l.cmd.rhs.ls.size != 2) {
            return toStep + (l.cmd.lhs to VROInt.nondetBool)
        } else if(l.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && l.cmd.rhs is TACExpr.BinOp.SignExtend &&
            l.cmd.rhs.o1 is TACExpr.Sym.Const && l.cmd.rhs.o2 is TACExpr.Sym.Var) {
            /*
               first things first, compute the bit we are extending
             */
            val idx = getExtendedBitIndex(l.cmd.rhs.o1.s.value) ?: return super.stepCommand(l, toStep, input, whole)
            val quals = treapSetOf<VROQuals>(
                VROQuals.SignExtended(
                    extendedBit = idx
                )).builder()
            input[l.cmd.rhs.o2.s]?.qual?.mapNotNull {
                it as? VROQuals.MultiplicationOf
            }?.mapTo(quals) {
                VROQuals.SignExtendedOfMultiplication(
                    extendedBit = idx,
                    op1 = it.op1,
                    op2 = it.op2,
                    sourceMultiplication = it.where,
                    signExtension = l.ptr
                )
            }
            return toStep + (l.cmd.lhs to VROInt(
                x = OpenInterval(Interval.IFull256),
                qual = quals.build()
            ))
        } else {
            return super.stepCommand(l, toStep, input, whole)
        }
    }

    /**
     * Update the state [S] with the new entry.
     */
    abstract operator fun S.plus(entry: Pair<TACSymbol.Var, VROInt>) : S

    /**
     * Trivial implementation which delegates to [expSemantics].
     */
    override fun stepExpression(
        lhs: TACSymbol.Var,
        rhs: TACExpr,
        toStep: S,
        input: S,
        whole: Any,
        l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
    ): S {
        return expSemantics.stepExpression(
            lhs, rhs, toStep, input, whole, l
        )
    }
}
