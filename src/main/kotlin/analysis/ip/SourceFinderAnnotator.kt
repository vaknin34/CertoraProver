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

package analysis.ip

import analysis.MustBeConstantAnalysis
import bridge.ContractInstanceInSDC
import bridge.LocalAssignmentSourceHint
import compiler.SourceIdentifier
import compiler.SourceSegment
import evm.MASK_SIZE
import utils.*
import vc.data.*
import java.math.BigInteger
import datastructures.stdcollections.*
import kotlin.streams.asSequence

/* See https://www.notion.so/certora/Logging-Solidity-in-calltrace-135fe5c14fd380eb8453cfd3c8629449?pvs=4
    for explanation about this magic constant and encoding
 */
val sourceAnnotationMask = BigInteger("ffffff6e4604afefe123321beef1b02fffffffffffffffffffffffff00000000", 16)
fun BigInteger.isSourceFinderConstant() = this == ((this and BigInteger("ffffffff", 16)) or sourceAnnotationMask)
val sourceAnnotationFlagMask = MASK_SIZE(16)

private data class SourceHint(val id: Int, val type: Int, val value: TACSymbol)

/**
 * Converts 'source finders' (see https://www.notion.so/certora/Logging-Solidity-in-calltrace-135fe5c14fd380eb8453cfd3c8629449?pvs=4)
 * to 'source hints' that can be processed by the call trace.
 * Note that it is very similar to the mechanism behind the InternalFunctionAnnotator
 */
object SourceFinderAnnotator {
    /**
     * looks for commands for the form `ByteStore(<mem address>, <magic constant>)`
     * that we instrumented in python land; replaces them with [SnippetCmd.EVMSnippetCmd.SourceFinderSnippet.LocalAssignmentSnippet]s for display in Call Trace
     */
    fun annotate(c: CoreTACProgram, source: ContractInstanceInSDC): CoreTACProgram {
        val constantAnalysis = MustBeConstantAnalysis(c.analysisCache.graph)

        val replacements = c.parallelLtacStream().mapNotNull { (ptr, cmd) ->
            if (cmd is TACCmd.Simple.AssigningCmd.ByteStore && cmd.base == TACKeyword.MEMORY.toVar()) {
                constantAnalysis.mustBeConstantAt(ptr, cmd.loc)
                    ?.takeIf { it.isSourceFinderConstant() }
                    ?.let { loc ->
                        ptr to SourceHint(
                            id = loc.and(sourceAnnotationFlagMask).toInt(),
                            type = loc.shiftRight(16).and(sourceAnnotationFlagMask).toInt(),
                            value = cmd.value
                        )
                    }
            } else {
                null
            }
        }.asSequence()

        val p = c.toPatchingProgram()
        replacements.forEach { (ptr, hint) ->
            val localAssignment = source.localAssignments[hint.id.toString()] ?: LocalAssignmentSourceHint(SourceIdentifier(-1,-1,-1), "?")
            p.replaceCommand(ptr,
                listOf(
                    SnippetCmd.EVMSnippetCmd.SourceFinderSnippet.LocalAssignmentSnippet(
                        localAssignment.lhs,
                        hint.type,
                        SourceSegment.resolveFromContext(source.origSrcContext, localAssignment.sourceLoc)?.range,
                        hint.value
                    ).toAnnotation()
                )
            )
        }
        return p.toCodeNoTypeCheck(c)
    }
}
