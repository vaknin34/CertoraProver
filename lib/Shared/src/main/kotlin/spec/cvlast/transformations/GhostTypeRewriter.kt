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

package spec.cvlast.transformations

import spec.cvlast.*
import spec.cvlast.CVLExp.HavocTarget.Companion.downcastToHavocTarget
import spec.cvlast.transformer.CVLCmdTransformer
import spec.cvlast.transformer.CVLExpTransformer
import utils.*
import utils.CollectingResult.Companion.bind
import utils.CollectingResult.Companion.flatten
import utils.CollectingResult.Companion.lift
import utils.CollectingResult.Companion.map
import utils.CollectingResult.Companion.transpose

/**
 * Rewrites occurrences of the `bytes` type in hooks and ghost declarations
 * to the (internal) type `bytesblob` (which represents a _hashed_ bytes)
 */
object GhostTypeRewriter {
    fun traverseAst(cvlAst: CVLAst): CollectingResult<CVLAst, Nothing> {
        return cvlAst.hooks.map {
            traverseHooks(it)
        }.flatten().bind { hooks ->
            cvlAst.copy(
            ghosts = cvlAst.ghosts.map {
                traverseGhostDeclaration(it)
            },
            hooks = hooks
        ).lift()}
    }

    private fun traverseHooks(it: CVLHook) : CollectingResult<CVLHook, Nothing> {
        return it.block.map {
                traverseHookBody(it)
            }.flatten().bind { m -> it.copy(
                block = m
        ).lift()}
    }

    private val expRewriter = object : CVLExpTransformer<Nothing> {
        override fun quant(exp: CVLExp.QuantifierExp): CollectingResult<CVLExp, Nothing> {
            val newType = if(isByteBlobCandidate(exp.qVarType)) {
                CVLType.PureCVLType.Primitive.HashBlob
            } else {
                exp.qVarType
            }
            return this.expr(exp.body).bind { cvlExp -> exp.copy(
                body = cvlExp,
                tag = exp.tag,
                param = exp.param.copy(
                    type = newType
                )
            ).lift() }
        }
    }

    fun isByteBlobCandidate(ty: CVLType) = ty is CVLType.PureCVLType.DynamicArray.Bytes1Array

    private val cmdRewriter = object : CVLCmdTransformer<Nothing>(CVLExpTransformer.copyTransformer()) {
        override fun havoc(cmd: CVLCmd.Simple.Havoc): CollectingResult<CVLCmd, Nothing> {
            val targets = cmd
                .targets
                .map { target -> expRewriter.expr(target.asExp) }
                .map { exp -> exp.downcastToHavocTarget() }
                .flatten()
            val assumingExp = cmd.assumingExp?.let(expRewriter::expr).transpose()

            return targets.map(assumingExp) { rewrittenTargets, rewrittenAssumingExp ->
                cmd.copy(targets = rewrittenTargets, assumingExp = rewrittenAssumingExp)
            }
        }
    }

    private fun traverseHookBody(it: CVLCmd) : CollectingResult<CVLCmd, Nothing> {
        return cmdRewriter.cmd(it)
    }

    private fun traverseGhostDeclaration(it: CVLGhostDeclaration) : CVLGhostDeclaration {
        return when(it) {
            is CVLGhostDeclaration.Function -> {
                it.copy(
                        paramTypes = it.paramTypes.map { type -> traverseType(type) },
                        ret = traverseType(it.ret)
                )
            }
            is CVLGhostDeclaration.Variable -> {
                it.copy(
                    type = traverseType(it.type)
                )
            }

            is CVLGhostDeclaration.Sum -> error("There can be no explicit references to a ghost summary in cvl")
        }

    }

    private fun traverseType(it: CVLType.PureCVLType) : CVLType.PureCVLType {
        return if(isByteBlobCandidate(it)) {
            CVLType.PureCVLType.Primitive.HashBlob
        } else if(it is CVLType.PureCVLType.Ghost) {
            when(it) {
                is CVLType.PureCVLType.Ghost.Function -> {
                    return it.copy(
                        inParams = it.inParams.map(this::traverseType),
                        outParam = traverseType(it.outParam)
                    )
                }
                is CVLType.PureCVLType.Ghost.Mapping -> {
                    it.copy(
                        key = traverseType(it.key),
                        value = traverseType(it.value)
                    )
                }
            }
        } else {
            it
        }
    }

}
