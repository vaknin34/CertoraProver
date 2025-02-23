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

package spec.cvlast

import config.Config
import spec.cvlast.transformer.CVLAstTransformer
import spec.cvlast.transformer.CVLCmdTransformer
import spec.cvlast.transformer.CVLExpTransformer
import spec.cvlast.typechecker.CVLError
import utils.CollectingResult
import utils.CollectingResult.Companion.asError
import utils.CollectingResult.Companion.lift
import utils.CollectingResult.Companion.map
import utils.CollectingResult.Companion.ok
import utils.VoidResult

private const val topLevelOnlyError = "Without grounding enabled, cannot use direct storage comparisons except in an assertion command."

private const val equalityOnlyMessage = "Without grounding enabled, only assertions of storage equality are allowed."

private fun CVLExp.isStorageOperand() = this.getCVLTypeOrNull() is CVLType.PureCVLType.VMInternal.BlockchainState ||
    this.getCVLTypeOrNull() is CVLType.PureCVLType.VMInternal.StorageReference

object StorageComparisonChecker : CVLAstTransformer<CVLError>(
    object : CVLCmdTransformer<CVLError>(object : CVLExpTransformer<CVLError> {
        override fun relop(exp: CVLExp.RelopExp): CollectingResult<CVLExp.RelopExp, CVLError> {
            return if(exp.r.isStorageOperand() || exp.l.isStorageOperand()) {
                CVLError.Exp(exp = exp, message = topLevelOnlyError).asError()
            } else {
                super.relop(exp)
            }
        }
    }) {
        override fun assertCmd(cmd: CVLCmd.Simple.Assert): CollectingResult<CVLCmd, CVLError> {
            if(cmd.exp is CVLExp.RelopExp && cmd.exp.r.isStorageOperand()) {
                return if (cmd.exp.relop == CVLExp.RelopExp.CVLERelop.EQ) {
                    cmd.lift()
                } else {
                    CVLError.Exp(
                        exp = cmd.exp,
                        message = equalityOnlyMessage
                    ).asError()
                }
            }
            return super.assertCmd(cmd)
        }
    }
) {
    fun CVLExp.isStorageOperand() = this.getCVLTypeOrNull() is CVLType.PureCVLType.VMInternal.BlockchainState ||
        this.getCVLTypeOrNull() is CVLType.PureCVLType.VMInternal.StorageReference

    override fun ast(ast: CVLAst): CollectingResult<CVLAst, CVLError> {
        return if(Config.GroundQuantifiers.get()) {
            ast.lift()
        } else {
            super.ast(ast)
        }
    }

    fun check(ast: CVLAst): VoidResult<CVLError> = ast(ast).map { ok }
}
