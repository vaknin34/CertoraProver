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

package smt.axiomgenerators.fullinstantiation.expnormalizer

import datastructures.stdcollections.*
import evm.*
import smt.HashingScheme
import smt.solverscript.LExpressionFactory
import smt.solverscript.SmtTheory
import smt.solverscript.functionsymbols.*
import tac.Tag
import utils.*
import vc.data.LExpression
import vc.data.lexpression.*
import java.math.BigInteger

/**
 * Used for translating to an integer arithmetic logic.
 * By default, all non-linear functions are linearized, passing `{ false }` [linearizationSelector] yields a non-linear
 * encoding. If a non-trivial [linearizationSelector] is given, only terms where the selector returns true are
 * linearized.
 */
class ExpNormalizerIA(
    lExpressionFactory: LExpressionFactory,
    targetTheory: SmtTheory,
    hashingScheme: HashingScheme,
    private val linearizationSelector: (LExpression) -> Boolean = { true }
) : ExpNormalizer(lExpressionFactory, targetTheory, hashingScheme) {

    init {
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.SimpleAddModulo)
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Bitwise.UninterpShiftRightLogical)
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Bitwise.UninterpShiftRightArithmetical)
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Bitwise.UninterpShiftLeft)
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Bitwise.UninterpBwAnd)
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Bitwise.UninterpBwOr)
        lxf.registerFunctionSymbol(AxiomatizedFunctionSymbol.Bitwise.UninterpBwXOr)
    }

    companion object {
        /** Checks if all the expressions in [args] have at most one non-constant (non-literal) element. Thus, assuming
         * they are operands to a multiplication (not checking that), the multiplication is still an instance of linear
         * arithmetic. */
        fun atMostOneNonConstant(args: List<LExpression>) = args.count { !it.isConst } <= 1
    }

    /**
     * Returns LExpression for checking if [e] is a positive signed int, i.e.
     * [LExpression] for "e <= 2^255 - 1 (MAX_EVM_INT256)".
     *
     * @param e: input LExpression
     * @return LExpression for "e <= 2^255 - 1"
     */
    private fun isPositiveSignedInt(e: LExpression) = lxf { e intLe litInt(MAX_EVM_INT256) }
    private fun isNegativeSignedInt(e: LExpression) = lxf { e intGt litInt(MAX_EVM_INT256) }
    private fun areOfSameSign(e1: LExpression, e2: LExpression) = lxf {
        isPositiveSignedInt(e1) eq isPositiveSignedInt(e2)
    }

    /**
     * Return `exp mod 2^256`, either using the explicit integer modulo or using our uninterpreted linearization
     * function.
     */
    private fun applyModulo(exp: LExpression) = lxf {
        if (linearizationSelector(exp)) {
            uninterpMod256(exp)
        } else {
            exp intMod TwoTo256
        }
    }

    /**
     * Should be applied on lexpressions that are in the range [0..2^256-1]
     */
    private fun convertFrom2s(x: LExpression) = lxf {
        if (x.isConst) {
            litInt(x.asConst.from2s())
        } else {
            ite(isPositiveSignedInt(x), x, x intSub TwoTo256)
        }
    }

    /**
     * Returns an lexpression of the condition that `op(arg1, arg2)` doesn't over or under flow in the signed sense,
     * when arg1 and arg2 are given in 2s complement
     */
    private fun noSignedOverflow(arg1: LExpression, arg2: LExpression, op: (LExpression, LExpression) -> LExpression) =
        with(lxf) {
            val res = op(convertFrom2s(arg1), convertFrom2s(arg2))
            and(
                res intLe litInt(MAX_EVM_INT256), // over
                res intGe litInt(MIN_EVM_INT256_AS_MATH_INT) // under
            )
        }

    fun isDefinitelyBit256(exp: LExpression) =
        (exp is LExpression.Identifier && exp.tag == Tag.Bit256) ||
            (exp.isNumericLiteral && BigInteger.ZERO <= exp.asConst && exp.asConst <= MAX_EVM_UINT256)

    private fun Tag.toInt(): Tag = when (this) {
        is Tag.Bits, Tag.Int -> Tag.Int
        is Tag.GhostMap -> Tag.GhostMap(
            paramSorts.map { it.toInt() },
            resultSort.toInt()
        )
        is Tag.UserDefined.Struct,
        is Tag.TransientTag -> error("should not be treating $this as values in SMT")
        else -> this
    }

    override val functionSymbolNormalizer = object : ContextLExpressionTransformer() {
        override fun literalPre(lit: LExpression.Literal) =
            lit.copy(tag = lit.tag.toInt()).lift()
        override fun identifierPre(id: LExpression.Identifier) =
            id.copy(tag = id.tag.toInt()).lift()
        override fun applyExprPost(exp: ApplyExpr): IntermediateLExp? = when (exp.f) {
            is NonSMTInterpretedFunctionSymbol -> when (exp.f) {
                is NonSMTInterpretedFunctionSymbol.Nullary.Nondet -> null

                is NonSMTInterpretedFunctionSymbol.Unary.BitwiseNot -> {
                    /**
                     * This code models bitwise not using intsub and the constant maxBv256. alternatively, we
                     * could use the function symbol uninterp_bwnot, and axiomatize it separately
                     *
                     * replaceByUninterpretedIfNecessary(originalExp)
                     */
                    val const = when (val tag = exp.f.signature.getParamSort(0)) {
                        is Tag.Bits -> tag
                        Tag.Int -> Tag.Bit256
                        else -> error("Not sure how to apply bitwise not to $exp.arg")
                    }.maxUnsigned
                    lxf { litInt(const) intSub exp.arg }.lift()
                }
                is NonSMTInterpretedFunctionSymbol.Unary.Extract ->
                    throw UnsupportedOperationException("extract for integer arithmetic not yet implemented")
                is NonSMTInterpretedFunctionSymbol.Unary.SignedPromote -> lxf {
                    ite(
                        exp.arg le litInt(exp.f.from.maxSigned),
                        exp.arg,
                        exp.arg + litInt(exp.f.to.maxUnsigned - exp.f.from.maxUnsigned)
                    )
                }.lift()

                is NonSMTInterpretedFunctionSymbol.Unary.UnsignedPromote -> exp.arg.lift()
                is NonSMTInterpretedFunctionSymbol.Unary.SafeMathNarrow -> exp.arg.lift()
                is NonSMTInterpretedFunctionSymbol.Unary.SafeSignedNarrow -> lxf {
                    ite(
                        exp.arg le litInt(exp.f.from.maxSigned),
                        exp.arg,
                        exp.arg + litInt(exp.f.to.maxUnsigned - exp.f.from.maxUnsigned)
                    )
                }.lift()
                is NonSMTInterpretedFunctionSymbol.Unary.SafeUnsignedNarrow -> exp.arg.lift()

                is NonSMTInterpretedFunctionSymbol.Binary.AssignEq ->
                    exp.copy(f = TheoryFunctionSymbol.Binary.Eq(exp.f.tag.toInt()))
                is NonSMTInterpretedFunctionSymbol.Binary.Sub -> lxf {
                    applyExp(
                        AxiomatizedFunctionSymbol.SimpleSubModulo,
                        applyExp(
                            TheoryFunctionSymbol.Binary.IntSub,
                            exp.args.mapIndexed { id, arg ->
                                val original = (context as LExpression.ApplyExpr).args[id]
                                arg.letIf(!isDefinitelyBit256(original)) {
                                    // see comment on `Add`.
                                    // the reason we don't do the mod outside the minus, is that most likely
                                    // these are actually bv256 vars, and so this % is a no-op and easy for
                                    // the solvers.
                                    it % TwoTo256
                                }
                            },
                            exp.meta
                        )
                    ).lift()
                }
                is NonSMTInterpretedFunctionSymbol.Binary.Div ->
                    exp.copy(f =
                        if (linearizationSelector(context)) {
                            AxiomatizedFunctionSymbol.UninterpDiv
                        } else {
                            TheoryFunctionSymbol.Binary.IntDiv.IntDivAllowNormalize
                        }
                    )
                is NonSMTInterpretedFunctionSymbol.Binary.Mod ->
                    exp.copy(f =
                        if (linearizationSelector(context)) {
                            AxiomatizedFunctionSymbol.UninterpMod
                        } else {
                            TheoryFunctionSymbol.Binary.IntMod.IntModAllowNormalize
                        }
                    )
                is NonSMTInterpretedFunctionSymbol.Binary.SMod ->
                    exp.copy(f = AxiomatizedFunctionSymbol.UninterpSMod)
                is NonSMTInterpretedFunctionSymbol.Binary.Exp -> lxf {
                    exp.copy(f = AxiomatizedFunctionSymbol.UninterpExp(exp.lhs.tag)).toLExpression() % TwoTo256
                }.lift()
                is NonSMTInterpretedFunctionSymbol.Binary.ShiftLeft ->
                    exp.copy(f = AxiomatizedFunctionSymbol.Bitwise.UninterpShiftLeft)
                is NonSMTInterpretedFunctionSymbol.Binary.ShiftRightLogical ->
                    exp.copy(f = AxiomatizedFunctionSymbol.Bitwise.UninterpShiftRightLogical)
                is NonSMTInterpretedFunctionSymbol.Binary.ShiftRightArithmetical ->
                    exp.copy(f = AxiomatizedFunctionSymbol.Bitwise.UninterpShiftRightArithmetical)
                is NonSMTInterpretedFunctionSymbol.Binary.Lt ->
                    exp.copy(f = TheoryFunctionSymbol.Binary.IntLt)
                is NonSMTInterpretedFunctionSymbol.Binary.Slt -> lxf {
                    or(
                        isNegativeSignedInt(exp.lhs) and isPositiveSignedInt(exp.rhs),
                        areOfSameSign(exp.lhs, exp.rhs) and (exp.lhs intLt exp.rhs)
                    )
                }.lift()
                is NonSMTInterpretedFunctionSymbol.Binary.Sle -> lxf {
                    or(
                        isNegativeSignedInt(exp.lhs) and isPositiveSignedInt(exp.rhs),
                        areOfSameSign(exp.lhs, exp.rhs) and (exp.lhs intLe exp.rhs)
                    )
                }.lift()
                is NonSMTInterpretedFunctionSymbol.Binary.Sgt -> lxf {
                    or(
                        isPositiveSignedInt(exp.lhs) and isNegativeSignedInt(exp.rhs),
                        areOfSameSign(exp.lhs, exp.rhs) and (exp.lhs intGt exp.rhs)
                    )
                }.lift()
                is NonSMTInterpretedFunctionSymbol.Binary.Sge -> lxf {
                    or(
                        isPositiveSignedInt(exp.lhs) and isNegativeSignedInt(exp.rhs),
                        areOfSameSign(exp.lhs, exp.rhs) and (exp.lhs intGe exp.rhs)
                    )
                }.lift()
                is NonSMTInterpretedFunctionSymbol.Binary.Gt ->
                    exp.copy(f = TheoryFunctionSymbol.Binary.IntGt)
                is NonSMTInterpretedFunctionSymbol.Binary.Le ->
                    exp.copy(f = TheoryFunctionSymbol.Binary.IntLe)
                is NonSMTInterpretedFunctionSymbol.Binary.Ge ->
                    exp.copy(f = TheoryFunctionSymbol.Binary.IntGe)
                is NonSMTInterpretedFunctionSymbol.Binary.BitwiseAnd ->
                    exp.copy(f = AxiomatizedFunctionSymbol.Bitwise.UninterpBwAnd)
                is NonSMTInterpretedFunctionSymbol.Binary.BitwiseOr ->
                    exp.copy(f = AxiomatizedFunctionSymbol.Bitwise.UninterpBwOr)
                is NonSMTInterpretedFunctionSymbol.Binary.BitwiseXor ->
                    exp.copy(f = AxiomatizedFunctionSymbol.Bitwise.UninterpBwXOr)
                is NonSMTInterpretedFunctionSymbol.Binary.NoAddOverflow -> lxf {
                    exp.copy(f = TheoryFunctionSymbol.Vec.IntAdd).toLExpression()  intLt TwoTo256
                }.lift()
                is NonSMTInterpretedFunctionSymbol.Binary.NoMulOverflow ->
                    if (atMostOneNonConstant(exp.args) || !linearizationSelector(context)) {
                        lxf { exp.copy(f = TheoryFunctionSymbol.Vec.IntMul.IntMulAllowNormalize).toLExpression() intLt TwoTo256 }
                    } else {
                        lxf { exp.copy(f = AxiomatizedFunctionSymbol.UninterpMul).toLExpression() intLt TwoTo256 }
                    }.lift()
                is NonSMTInterpretedFunctionSymbol.Binary.NoSMulOverUnderflow ->
                    if (atMostOneNonConstant(exp.args) || !linearizationSelector(context)) {
                        noSignedOverflow(exp.lhs, exp.rhs) { a, b -> lxf { a * b } }
                    } else {
                        noSignedOverflow(exp.lhs, exp.rhs) { a, b -> lxf { a uninterpMul b } }
                    }.lift()
                is NonSMTInterpretedFunctionSymbol.Binary.NoSAddOverUnderflow ->
                    noSignedOverflow(exp.lhs, exp.rhs) { a, b -> lxf { a + b } }.lift()
                is NonSMTInterpretedFunctionSymbol.Binary.NoSSubOverUnderflow ->
                    noSignedOverflow(exp.lhs, exp.rhs) { a, b -> lxf { a - b } }.lift()
                is NonSMTInterpretedFunctionSymbol.Binary.Concat ->
                    throw UnsupportedOperationException("concat for integer arithmetic not yet implemented")

                is NonSMTInterpretedFunctionSymbol.Vec.Add -> {
                    val (bit256s, mathints) = exp.args
                        .zip((context as LExpression.ApplyExpr).args)
                        .partition { isDefinitelyBit256(it.second) }
                        .let { (f, s) -> f.map { it.first } to s.map { it.first } }
                    val mathIntSum =
                        if (mathints.isNotEmpty()) {
                            listOf(
                                lxf {
                                    // We take the exact modulo here and not the uninterpreted one.
                                    // Otherwise any `Add` would prevent us from using a LIA only race.
                                    // Anyway, mathints being added via `Add` and not `IntAdd` are probably rare.
                                    mathints.reduce { a, b -> a + b } % TwoTo256
                                }
                            )
                        } else {
                            emptyList()
                        }
                    (bit256s + mathIntSum).reduce { arg1, arg2 ->
                        lxf { applyExp(AxiomatizedFunctionSymbol.SimpleAddModulo, arg1 + arg2) }
                    }.lift()
                }
                is NonSMTInterpretedFunctionSymbol.Vec.Mul ->
                    applyModulo(
                        if (atMostOneNonConstant(exp.args) || !linearizationSelector(context)) {
                            exp.copy(f = TheoryFunctionSymbol.Vec.IntMul.IntMulAllowNormalize).toLExpression()
                        } else {
                            lxf.buildAppExpFoldVecToBinary(AxiomatizedFunctionSymbol.UninterpMul, exp.args, exp.meta)
                        }
                    ).lift()

                is NonSMTInterpretedFunctionSymbol.Hash -> null
                is NonSMTInterpretedFunctionSymbol.MultiDimArray -> null

                is NonSMTInterpretedFunctionSymbol.Ternary.MulMod -> {
                    if (linearizationSelector(context)) {
                        lxf { (exp.args[0] uninterpMul exp.args[1]) uninterpMod exp.args[2] }
                    } else {
                        lxf { (exp.args[0] intMul exp.args[1]) intMod exp.args[2] }
                    }.lift()
                }
                is NonSMTInterpretedFunctionSymbol.Ternary.AddMod -> {
                    if (linearizationSelector(context)) {
                        lxf { (exp.args[0] intAdd exp.args[1]) uninterpMod exp.args[2] }
                    } else {
                        lxf { (exp.args[0] intAdd exp.args[1]) intMod exp.args[2] }
                    }.lift()
                }
            }
            is TheoryFunctionSymbol -> when (exp.f) {
                is TheoryFunctionSymbol.Binary.IntDiv.IntDivAllowNormalize ->
                    runIf(linearizationSelector(context) && !exp.args[1].isConst) {
                        exp.copy(f = AxiomatizedFunctionSymbol.UninterpDiv)
                    }

                is TheoryFunctionSymbol.Binary.IntMod.IntModAllowNormalize ->
                    runIf(linearizationSelector(context) && !exp.rhs.isConst) {
                        exp.copy(f = AxiomatizedFunctionSymbol.UninterpMod)
                    }
                is TheoryFunctionSymbol.Binary.Eq ->
                    exp.copy(f = exp.f.copy(tag = exp.f.tag.toInt()))
                is TheoryFunctionSymbol.Ternary.Ite ->
                    exp.copy(f = TheoryFunctionSymbol.Ternary.Ite(exp.f.tag.toInt()))
                is TheoryFunctionSymbol.Vec.IntMul.IntMulAllowNormalize ->
                    runIf(!atMostOneNonConstant(exp.args) && linearizationSelector(context)) {
                        lxf.buildAppExpFoldVecToBinary(AxiomatizedFunctionSymbol.UninterpMul, exp.args, exp.meta).lift()
                    }
                else -> null
            }
            is ConstantSymbol -> null
            is UserDefinedFunctionSymbol -> null
            is ArraySelectFunctionSymbol.OneDim ->
                exp.copy(f = exp.f.copy(signature = exp.f.signature.transform { it.toInt() }))
            is ArraySelectFunctionSymbol.MultiDim ->
                exp.copy(f = exp.f.copy(signature = exp.f.signature.transform { it.toInt() }))
            is AxiomatizedFunctionSymbol -> when (exp.f) {
                is AxiomatizedFunctionSymbol.SKeyDt ->
                    exp.copy(f = normalizeSKeyDtFS(exp.f))
                is AxiomatizedFunctionSymbol.Hash.SimpleHashN ->
                    exp.copy(f = exp.f.copy(tag = exp.f.tag.toInt()))
                is AxiomatizedFunctionSymbol.Bitwise.SignExtend ->
                    exp.copy(f = exp.f.copy(tag = exp.f.tag.toInt()))
                is AxiomatizedFunctionSymbol.UninterpExp ->
                    exp.copy(f = exp.f.copy(tag = exp.f.tag.toInt()))
                is AxiomatizedFunctionSymbol.DefFunc ->
                    exp.copy(f = normalizeFunctionSymbol(exp.f))
                else -> null
            }
            else -> null
        }
    }

    fun normalizeSKeyDtFS(f: AxiomatizedFunctionSymbol.SKeyDt): AxiomatizedFunctionSymbol.SKeyDt = when (f) {
        is AxiomatizedFunctionSymbol.SKeyDt.Basic -> f.copy(tag = f.tag.toInt())
        is AxiomatizedFunctionSymbol.SKeyDt.SkeyNode -> f
        is AxiomatizedFunctionSymbol.SKeyDt.SkeyAdd -> f.copy(tag = f.tag.toInt())
        is AxiomatizedFunctionSymbol.SKeyDt.ToSkey -> f.copy(tag = f.tag.toInt())
        is AxiomatizedFunctionSymbol.SKeyDt.FromSkey -> f.copy(tag = f.tag.toInt())
        is AxiomatizedFunctionSymbol.SKeyDt.SKeySelector ->
            f.copy(tag = f.tag.toInt(), constructor = normalizeSKeyDtFS(f.constructor))
    }

    override fun normalizeFunctionSymbol(fs: FunctionSymbol): FunctionSymbol = when (fs) {
        is AxiomatizedFunctionSymbol.SKeyDt -> normalizeSKeyDtFS(fs)

        is AxiomatizedFunctionSymbol.DefFunc ->
            fs.copy(signature = fs.signature.transform { it.toInt() })
        else -> fs
    }
}
