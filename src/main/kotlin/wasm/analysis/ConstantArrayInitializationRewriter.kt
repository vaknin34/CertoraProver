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

package wasm.analysis

import analysis.CommandWithRequiredDecls.Companion.mergeMany
import analysis.snarrowOrNull
import datastructures.stdcollections.*
import log.*
import tac.*
import utils.*
import vc.data.*
import wasm.host.soroban.opt.LONG_COPY_STRIDE
import wasm.tacutils.*
import java.math.BigInteger
import java.util.stream.Collectors

private val logger = Logger(LoggerTypes.WASM)

/**
 * Replace loops summarized by [ConstArrayInitSummary] with simple assignments. That is, if we have
 * a _valid_ (as defined by [ConstArrayInitSummary.isValidSimpleInitialization]) summarized loop
 *
 *   for (i in 0..len) { Mem[ptr + i] := c },
 *
 * then we replace this with
 *
 *   Mem[ptr:ptr+len*elementSize] = [ i |-> if i%elemSize = 0 then c else * ]
 *
 * in TAC:
 *
 * START:
 *   A = *
 *   I = 0
 *   JUMP HEAD
 *
 * HEAD:
 *   B = I < K
 *   JUMP B LOOP DONE
 *
 * LOOP:
 *   P = A + I
 *   M[P] = C
 *   TMP = I + Stride
 *   I = TMP
 *   JUMP HEAD
 *
 *  DONE:
 *    ...
 *
 * Is all replaced with (assuming exists some Len s.t. K = Stride*Len)
 *
 * START:
 *   A = *
 *   M[A:K] = [ i |-> if i % Stride = 0 then C else *]
 *   JUMP DONE
 *
 * Done:
 *   ...
 *
 */
object ConstantArrayInitializationRewriter {
    fun unrollStaticLoops(ctp: CoreTACProgram): CoreTACProgram {
        val g = ctp.analysisCache.graph

        val initLoops = ctp.parallelLtacStream().mapNotNull { cmd ->
            cmd.ptr `to?` cmd.snarrowOrNull<ConstArrayInitSummary>()
        }.collect(Collectors.toSet())

        return ctp.patching { patching ->
            for ((ptr, init) in initLoops) {
                if (!init.isValidSimpleInitialization(g)) {
                    logger.warn { "$init not valid"  }
                    patching.replace(ptr) { _ ->
                        listOf(TACCmd.Simple.JumpCmd(init.originalBlockStart))
                    }
                } else {
                    val bytes = TACKeyword.TMP(Tag.ByteMap)
                    patching.addVarDecl(bytes)

                    val startLoc = TACKeyword.TMP(Tag.Bit256)
                    // We only define elementSize aligned locations,
                    // as this reflects the original loop striding behavior
                    val const = mergeMany(
                        defineMap(
                            bytes,
                        ) { i ->
                            ite(
                                i = (i[0] mod init.stride.asTACExpr) eq BigInteger.ZERO.asTACExpr,
                                t = init.v,
                                e = unconstrained(Tag.Bit256)
                            )
                        },
                        assign(startLoc) {
                            init.startPtr.asSym().add(init.constantOffset.asTACExpr)
                        }
                    )
                    patching.addVarDecls(const.varDecls)

                    val summ = TACCmd.Simple.ByteLongCopy(
                        srcBase = bytes,
                        dstBase = TACKeyword.MEMORY.toVar(),
                        dstOffset = startLoc,
                        srcOffset = BigInteger.ZERO.asTACSymbol(),
                        length = (init.stride * init.iterations).asTACSymbol(),
                        meta = init.stride.toIntOrNull()?.let { MetaMap(LONG_COPY_STRIDE to it) } ?: MetaMap()
                    )
                    patching.replace(ptr) { _ ->
                        const.cmds +
                            listOf(
                                summ,
                                TACCmd.Simple.JumpCmd(init.skipTarget)
                            )
                    }

                    // Delete the loop
                    patching.consolidateEdges(init.skipTarget, listOf(init.originalBlockStart), object : PatchingTACProgram.CommandRemapper<TACCmd.Simple> {
                        override fun isJumpCommand(c: TACCmd.Simple): Boolean {
                            return PatchingTACProgram.SIMPLE.isJumpCommand(c)
                        }

                        override fun remapSuccessors(c: TACCmd.Simple, remapper: (NBId) -> NBId): TACCmd.Simple {
                            check(c is TACCmd.Simple.SummaryCmd)
                            return TACCmd.Simple.JumpCmd(init.skipTarget)
                        }
                    })
                }
            }
        }
    }
}
