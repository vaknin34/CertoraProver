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

package instrumentation.transformers

import analysis.*
import analysis.EthereumVariables.extcodesize
import analysis.EthereumVariables.simplifyExtcodesize
import com.certora.collect.*
import config.Config
import tac.Tag
import utils.letIf
import utils.mapNotNull
import vc.data.*
import vc.data.SimplePatchingProgram.Companion.patchForEach
import vc.data.TACProgramCombiners.andThen
import vc.data.tacexprutil.ExprUnfolder
import java.math.BigInteger

class EnvironmentFixer(private val address: BigInteger, private val isConstructor: Boolean) : CodeTransformer() {
    override fun transform(ast: CoreTACProgram) : CoreTACProgram {
        val tmpSymbol = TACKeyword.TMP(Tag.Bit256)

        val addressVar = EthereumVariables.address.at(callIndex = 0)
        val fixedEnv = if(!isConstructor) {
            simplifyExtcodesize(TACCmd.EVM.AssignExtcodesizeCmd(tmpSymbol, addressVar)).merge(
                ExprUnfolder.unfoldPlusOneCmd("codeSize", TACExprFactTypeCheckedOnlyPrimitives.Gt(
                    tmpSymbol.asSym(), TACExpr.zeroExpr
                )) {
                    TACCmd.Simple.AssumeCmd(it.s)
                }
            ).merge(tmpSymbol, addressVar)
        } else {
            CommandWithRequiredDecls(
                TACCmd.Simple.WordStore(
                    base = extcodesize,
                    loc = addressVar,
                    value = TACSymbol.Zero
                ),
                setOf(extcodesize, addressVar)
            )
        }

        return ast.prependToBlock0(fixedEnv).letIf(isConstructor) { prog ->
            val sinks = prog.analysisCache.graph.sinks
            prog.ltacStream().mapNotNull {
                it.maybeNarrow<TACCmd.Simple.ReturnCmd>()
            }.patchForEach(prog, check = false) { retCmd ->
                check(retCmd.wrapped in sinks) {
                    "Have return command that is not a return"
                }
                val modelReturn : CommandWithRequiredDecls<TACCmd.Simple> = CommandWithRequiredDecls<TACCmd.Simple>(listOf(
                    TACCmd.Simple.WordStore(
                        base = extcodesize,
                        loc = addressVar,
                        value = retCmd.cmd.length
                    )
                ), treapSetOf()).letIf(Config.PreciseCodedataSemantics.get()) { extSet ->
                    val codeData = EthereumVariables.getCodeData(address)
                    val codeSize = EthereumVariables.getCodeDataSize(address)
                    extSet andThen CommandWithRequiredDecls<TACCmd.Simple>(listOf(
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            lhs = codeSize.withMeta(TACMeta.NO_CODE_REWRITE),
                            rhs = retCmd.cmd.length
                        ),
                        TACCmd.Simple.ByteLongCopy(
                            dstBase = codeData.withMeta(TACMeta.NO_CODE_REWRITE),
                            dstOffset = TACSymbol.Zero,
                            length = retCmd.cmd.length,
                            srcOffset = retCmd.cmd.sourceOffset,
                            srcBase = retCmd.cmd.sourceBase
                        )
                    ), treapSetOf(retCmd.cmd.length, codeData, codeSize, retCmd.cmd.sourceBase, retCmd.cmd.sourceBase))
                }.merge(retCmd.cmd)
                this.replaceCommand(retCmd.ptr, modelReturn)
            }
        }

    }
}
