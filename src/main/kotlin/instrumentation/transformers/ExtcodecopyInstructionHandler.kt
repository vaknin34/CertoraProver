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

import analysis.icfg.ExpressionSimplifier
import analysis.maybeNarrow
import log.Logger
import log.LoggerTypes
import optimizer.resolveBytecodeRange
import scene.IScene
import utils.`to?`
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACMeta
import vc.data.TACSymbol
import verifier.SimpleMemoryOptimizer

private val logger = Logger(LoggerTypes.COMMON)

/**
 * A lousy attempt to do something with extcodecopy which is a map from addresses to ByteMaps.
 * We don't support those in TAC and currently (June 2023) there wasn't a compelling reason to in the last 4 1/2 years!
 * But we do want to be sound.
 */
object ExtcodecopyInstructionHandler {

    fun work(c: CoreTACProgram, scene: IScene): CoreTACProgram {
        val graph = c.analysisCache.graph
        val patch = c.toPatchingProgram()
        // go over all commands and look for ByteLongCopys whose base is extcodedata
        val extcodedataReadsAndVars = graph.commands
            .mapNotNull { it.maybeNarrow<TACCmd.Simple.ByteLongCopy>()?.let { it `to?` it.cmd.srcBase.meta[TACMeta.EXTCODE_DATA_KEY] } }

        // if we have consts, we can read from the scene.
        // if not, we at least want to "havoc" the base we are reading from.
        extcodedataReadsAndVars.forEach { (extcodecopy, addr) ->

            when (addr) {
                is TACSymbol.Var -> extcodecopy.cmd.srcBase.toUnique().let { newSrcBase ->
                    patch.update(extcodecopy.ptr, extcodecopy.cmd.copy(srcBase = newSrcBase))
                    patch.addVarDecl(newSrcBase)
                }

                is TACSymbol.Const -> {
                    val newSrcBase = extcodecopy.cmd.srcBase.withSuffix(addr.value.toString(16))
                    patch.addVarDecl(newSrcBase)
                    scene.getContractOrNull(addr.value)?.bytecode?.bytes?.let { bytecode ->
                        (extcodecopy.cmd.srcOffset as? TACSymbol.Const)?.let { offset ->
                            (extcodecopy.cmd.length as? TACSymbol.Const)?.let { size ->
                                resolveBytecodeRange(bytecode, offset.value, size.value)
                            }
                        }?.let { (str, hash) ->
                            // SG: I guess I don't know what to do with that info.
                            logger.warn { "Found that we read from extcodedata $extcodecopy the string $str with hash $hash" }
                            val cmd = extcodecopy.cmd
                            val replacement = SimpleMemoryOptimizer.rewriteByteLongCopyThatCopiesString(
                                str,
                                TACCmd.Simple.ByteLongCopy(
                                    cmd.dstOffset, cmd.srcOffset,
                                    cmd.length, cmd.dstBase,
                                    cmd.srcBase, cmd.meta),
                                extcodecopy.ptr,
                                ExpressionSimplifier(graph)
                            )
                            patch.addVarDecls(replacement.varDecls)
                            patch.replaceCommand(extcodecopy.ptr,
                                replacement.cmds
                            )
                        }
                    }
                    // and we're gonna havoc anyway, but with the address we know
                    patch.update(extcodecopy.ptr, extcodecopy.cmd.copy(srcBase = newSrcBase))

                }
            }
        }

        return patch.toCode(c)
    }
}
