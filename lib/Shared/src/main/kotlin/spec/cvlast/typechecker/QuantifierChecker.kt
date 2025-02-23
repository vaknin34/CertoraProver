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

package spec.cvlast.typechecker

import config.Config
import spec.CastType
import spec.cvlast.*
import utils.CollectingResult.Companion.asError
import utils.CollectingResult.Companion.bind
import utils.CollectingResult.Companion.ok
import utils.VoidResult
import utils.`impossible!`

/**
 * Quantified formulae utilize a completely different compilation paradigm than the rest of CVL. All CVL expressions
 * and sub-expressions are compiled into a three-address form. Thus, an expression may lead to some arbitrary TAC
 * program.
 *
 * However, in general we do not handle arbitrary within a quantified formula. Thus, instead of using the
 * CVLExpressionCompiler to compile the body of quantified formulae, we use CVLExpToTACExpr. However, this means
 * some {CVLExp]s are either impossible to compile, or we have not gotten around to implementing a non-three-address
 * style compilation.
 *
 * This class is an attempt to catch any case where CVLExpToTACExpr will fail to compile a [CVLExp] and produce an
 * actionable error for the user.
 */
object QuantifierChecker: CVLExpFolder<VoidResult<CVLError>>() {
    private const val POSTFIX = "are disallowed inside quantified formulas."
    private fun isStorageReference(exp: CVLExp) : VoidResult<CVLError> {
        return if(exp.getCVLType() is CVLType.PureCVLType.VMInternal.StorageReference) {
            CVLError.Exp(
                exp = exp, "Storage comparison references $POSTFIX"
            ).asError()
        } else {
            ok
        }
    }

    override fun castExpression(acc: VoidResult<CVLError>, exp: CVLExp.CastExpr): VoidResult<CVLError> {
        return super.castExpression(acc, exp).bind(
            when (exp.castType) {
                CastType.REQUIRE -> CVLError.Exp(exp, "Require casts $POSTFIX").asError()
                CastType.ASSERT -> CVLError.Exp(exp, "Assert casts $POSTFIX").asError()
                CastType.CONVERT,
                CastType.TO -> ok
            }
        )
    }

    override fun arrayderef(acc: VoidResult<CVLError>, exp: CVLExp.ArrayDerefExp): VoidResult<CVLError> {
        return super.arrayderef(acc, exp).bind(isStorageReference(exp))
    }

    override fun relop(acc: VoidResult<CVLError>, exp: CVLExp.RelopExp): VoidResult<CVLError> {
        /*
         NB we do not have to check for storage references here because that is handled in the array deref case
         NB also that we do not need to check both operands, because the typing rule for relops require that non-arithmetic
         types must be equal
         */
        return super.relop(acc, exp).bind {
            if(exp.r.getCVLTypeOrNull() is CVLType.PureCVLType.VMInternal.BlockchainState) {
                CVLError.Exp(exp, "Storage comparisons $POSTFIX").asError()
            } else {
                ok
            }
        }

    }

    override fun setmem(acc: VoidResult<CVLError>, exp: CVLExp.SetMemExp): VoidResult<CVLError> {
        return super.setmem(acc, exp).bind(CVLError.Exp(exp, "Set membership checks $POSTFIX").asError())
    }

    override fun applyExp(acc: VoidResult<CVLError>, exp: CVLExp.ApplyExp): VoidResult<CVLError> {
        return super.applyExp(acc, exp).bind(
            when (exp) {
                is CVLExp.ApplyExp.CVLFunction ->
                    DisallowedTypeUsedInQuantifier(
                        exp.getRangeOrEmpty(),
                        exp.toAppliedString(),
                        DisallowedTypeUsedInQuantifier.DisallowedType.CVL_FUNCTION_CALL
                    ).asError()
                is CVLExp.ApplyExp.ContractFunction -> {
                    if (!Config.AllowSolidityQuantifierCalls.get()) {
                        DisallowedTypeUsedInQuantifier(
                            exp.getRangeOrEmpty(),
                            exp.toAppliedString(),
                            DisallowedTypeUsedInQuantifier.DisallowedType.SOLIDITY_FUNCTION_CALL
                        ).asError()
                    } else {
                        ok
                    }
                }
                is CVLExp.ApplyExp.Definition,
                is CVLExp.ApplyExp.Ghost -> ok

                is CVLExp.ApplyExp.CVLBuiltIn -> when (exp.id) {
                    CVLBuiltInName.ECRECOVER -> ok
                    CVLBuiltInName.SHA256,
                    CVLBuiltInName.KECCAK256 -> DisallowedTypeUsedInQuantifier(
                        exp.getRangeOrEmpty(),
                        exp.toAppliedString(),
                        DisallowedTypeUsedInQuantifier.DisallowedType.BUILT_IN_KECCAK256
                    ).asError()

                    CVLBuiltInName.FOUNDRY_PRANK,
                    CVLBuiltInName.FOUNDRY_START_PRANK,
                    CVLBuiltInName.FOUNDRY_STOP_PRANK,
                    CVLBuiltInName.FOUNDRY_WARP,
                    CVLBuiltInName.FOUNDRY_MOCK_CALL,
                    CVLBuiltInName.FOUNDRY_CLEAR_MOCKED_CALLS -> `impossible!`
                }
            }
        )
    }

    override fun unary(acc: VoidResult<CVLError>, exp: CVLExp.UnaryExp): VoidResult<CVLError> {
        return super.unary(acc, exp).bind(
            when (exp) {
                is CVLExp.UnaryExp.BwNotExp -> CVLError.Exp(exp, "Bitwise not expressions $POSTFIX").asError()
                is CVLExp.UnaryExp.LNotExp -> ok
                is CVLExp.UnaryExp.UnaryMinusExp -> ok
            }
        )
    }


    override fun variable(acc: VoidResult<CVLError>, exp: CVLExp.VariableExp): VoidResult<CVLError> {
        return acc
    }
}
