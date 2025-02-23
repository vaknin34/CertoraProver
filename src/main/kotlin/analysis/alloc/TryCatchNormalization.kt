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

package analysis.alloc

import analysis.*
import datastructures.stdcollections.*
import evm.EVM_WORD_SIZE
import evm.MAX_EVM_UINT256
import tac.Tag
import utils.mapNotNull
import utils.`to?`
import vc.data.*
import vc.data.SimplePatchingProgram.Companion.patchForEach

/**
 * The compilation of try-catch in Solidity is a nightmare for us. When you do
 * `try ... catch Error(string memory message) { ... }`
 *
 * Solidity does the call and then switches on the RC. If it is false, it copies the entirety of the returndata
 * into caller's scratch. It then checks the 4-byte prefix of the hash to see if it matches Error(string). If so,
 * it validates that the remainder of the buffer is a valid ABI encoding of a string. That is,
 * we have:
 * offset, len, data
 *
 * where offset is a relative offset to len, and there are at least len bytes to hold data.
 *
 * If this is the case, Solidity does something awful.
 *
 * It generates the output of pointer of the "allocation" to be the location of `len` above in scratch buffer,
 * then sets the FP to be the end location of `data` in the above.
 *
 * In pseudo-code, we have:
 * ```
 * len = returnsize - 4
 * mem[fp:len] == returndata[4:len]
 * offset = mem[fp]
 * end = fp + len
 * if(offset + fp + 31 >= end) { revert; } // validate the offset
 * string_start = fp + offset
 * str_len = mem[string_start]
 * str_end = string_start + 32 + str_len
 * if(str_len >= end) { revert; } // validate the string length
 * output = fp + offset
 * fp = fp + round_up(offset + 32 + str_len)
 * ```
 *
 * where round_up rounds up it's argument to the nearest multiple of 32.
 *
 * This both destroys the allocation analysis, but the init analysis too (even if we somehow recognize the allocation pattern
 * here, we expect to see the initialization come after the allocation, here we're allocating an object "on top of"
 * a correctly initialized buffer).
 *
 * This is a HEURISTIC pass ot recognize this pattern, and rewrite the allocation and initialization to look like
 * a proper initialization. In particular, we detect a write of the FP that matches the pattern
 * ```
 * ROUND_UP(32 + LEN + START), where
 * LEN = MEM[FP + OFFSET]
 * START = FP + OFFSET
 * OFFSET = MEM[FP]
 * ROUND_UP(p) = (p + 31) & ~31
 * ```
 * These names roughly correspond to the actual [PatternMatcher.Pattern] instances below.
 *
 * Upon such a match, we rewrite the fp update to instead be:
 * S = FP
 * FP = S + ((LEN + 63) & ~31)
 * where `LEN` denotes the symbol that holds the result of matching on `LEN`, and S is the symbol
 * that holds the output pointer. We pick the variable name that holds the output pointer heuristically.
 * We heuristically choose the variable that was used to read the value of LEN;
 * that is, the output pointer is taken to be the operand `o` of `MEM[o]` in the match of `LEN`,
 * which must match `FP + OFFSET`, that is, the start of the string.
 * (Careful readers will note that we duplicate the `FP + OFFSET` pattern, both
 * of which could be the output of the allocation. Empirically
 * we see that Solidity does indeed ducpliate the computation, and it is the version
 * of the computation used in the read of the string length that is also is used as the
 * result of the allocation.)
 *
 * We also need to initialize the fake computation. We then add:
 * ```
 * MEM[S] = LEN
 * MEM[S + 32:LEN] = RETURNDATA[DATA_START:LEN]
 *
 * where `DATA_START` is the absolute offset of the string data within the returndata buffer. It is *not* correct
 * to assume that this is just `32 + 4` (4 for slicing off the sighash, 32 to include the size of the offset for
 * the string), although it will be in the majority of cases.
 *
 * We can, however, compute the absolute offset ourselves by:
 * `(S - FP) - 4 + 32`
 * Recall that FP effectively points to offset 4 within the returndata buffer, and thus, computing the offset of `S`
 * relative to `FP` gives the start location of the string within the returndata buffer, offset by 4. So, we subtract 4, but
 * then add back 32, because we want the start of the string data, not the start of the string data itself.
 *
 * Thus, our instrumentation is:
 *
 * ```
 * DATA_START = (S - FP) + 28 // fold the -4 + 32
 * S = FP
 * FP = S + ((LEN + 63) & ~31)
 * MEM[S] = LEN
 * MEM[S: 32:LEN] = RETURNDATA[DATA_START:LEN]
 * ```
 *
 * We check very few assumptions in the above process: we do check that the symbol chosen for `S` is live, and that
 * at the point we rewrite the allocation the variables chosen for `LEN` and `S` hold the same values as at their
 * match position. However, we don't check that the code is generating variables that remain live after this computation
 * or that the path conditions imply that the string is encoded properly.
 */
object TryCatchNormalization {
    private fun <T> PatternDSL.memoryReadOf(locPattern: PatternDSL.PatternBuilder<T>): PatternDSL.FunctionContinuation<T> = { _: LTACCmd, c: TACCmd.Simple.AssigningCmd ->
        (c as? TACCmd.Simple.AssigningCmd.ByteLoad)?.takeIf {
                it.base == TACKeyword.MEMORY.toVar()
            }?.loc
    }.lift<T>()(locPattern)

    private val PatternDSL.readFP : PatternDSL.PatternBuilder<CmdPointer> get() = Var { p, ltacCmd ->
        if(p == TACKeyword.MEM64.toVar()) {
            PatternMatcher.VariableMatch.Match(ltacCmd.ptr)
        } else {
            PatternMatcher.VariableMatch.Continue
        }
    }

    data class ReadAtFP(
        val readLoc: CmdPointer,
        val fpAccessLocation: CmdPointer
    )

    data class OffsetInfo(
        val fpAccessLoc: CmdPointer,
        val readInfo: ReadAtFP
    )

    data class LengthReadInfo(
        val offsetInfo: OffsetInfo,
        val readLoc: CmdPointer
    )

    private val PatternDSL.readAtFP : PatternDSL.PatternBuilder<ReadAtFP> get() =
        memoryReadOf(readFP).withAction { readLoc, fpRead ->
            ReadAtFP(
                readLoc = readLoc.ptr,
                fpAccessLocation = fpRead
            )
        }

    private val PatternDSL.stringStart get() = (readAtFP + readFP).commute.withAction { left, right ->
        OffsetInfo(
            fpAccessLoc = right,
            readInfo = left
        )
    }

    private val PatternDSL.lengthPattern get() =
        memoryReadOf(stringStart).withAction {  l, p ->
            LengthReadInfo(
                offsetInfo = p,
                readLoc = l.ptr
            )
        }

    private fun <T> PatternDSL.roundUp(v: PatternDSL.PatternBuilder<T>) = ((v + 31()).commute.first and Const(
        MAX_EVM_UINT256.andNot(31.toBigInteger()))).commute.first

    private val PatternDSL.ONE_WORD get() = Const(EVM_WORD_SIZE)

    private val PatternDSL.allocAmount get() = roundUp(commuteThree(ONE_WORD, lengthPattern, readAtFP, PatternDSL.CommutativeCombinator.add) { _, l, r ->
        l to r
    })

    private val returnBufferPattern = PatternDSL.build {
        (readFP + allocAmount).commute.withAction { fpRead, pair -> fpRead to pair } `^`
            commuteThree(ONE_WORD, stringStart, roundUp(lengthPattern), PatternDSL.CommutativeCombinator.add) { _, s, l ->
                s.fpAccessLoc to (l to s.readInfo)
            } `^`
            roundUp(commuteThree(ONE_WORD, stringStart, lengthPattern, PatternDSL.CommutativeCombinator.add) { _, s, l ->
                s.fpAccessLoc to (l to s.readInfo)
            })
    }

    fun normalizeTryCatch(c: CoreTACProgram) : CoreTACProgram {
        val graph = c.analysisCache.graph
        val allocMatcher = PatternMatcher.compilePattern(graph, returnBufferPattern)

        return c.parallelLtacStream().mapNotNull {
            it `to?` it.maybeNarrow<TACCmd.Simple.AssigningCmd>()?.takeIf {
                it.cmd.lhs == TACKeyword.MEM64.toVar()
            }?.let {
                allocMatcher.queryFrom(it).toNullableResult()
            }?.takeIf { (startReadLoc, endComputation) ->
                // that is, all of the parts of the pattern accessed the free pointer at the same location
                setOf(
                    startReadLoc,
                    endComputation.first.offsetInfo.fpAccessLoc,
                    endComputation.first.offsetInfo.readInfo.fpAccessLocation,
                    endComputation.second.fpAccessLocation
                ).size == 1
            }
        }.mapNotNull { (fpWrite, allocInfo) ->
            val (_, endComputation) = allocInfo
            val readLocation = graph.elab(endComputation.first.readLoc).narrow<TACCmd.Simple.AssigningCmd.ByteLoad>()
            // we are going to guess that this is the variable that solidity uses as the output pointer.
            val outputPointer = readLocation.cmd.loc as TACSymbol.Var
            val lengthSymbol = readLocation.cmd.lhs
            // ...or not I guess
            if(!graph.cache.lva.isLiveAfter(v = outputPointer, ptr = fpWrite.ptr)) {
                return@mapNotNull null
            }
            // good guess, but they changed the value :(
            if(outputPointer !in graph.cache.gvn.findCopiesAt(fpWrite.ptr, readLocation.ptr to outputPointer)) {
                return@mapNotNull null
            }

            // is our length still live?
            if(graph.cache.def.defSitesOf(v = lengthSymbol, pointer = fpWrite.ptr) != setOf(endComputation.first.readLoc)) {
                return@mapNotNull null
            }
            // we have the tools to rewrite the allocation
            val bump = TACKeyword.TMP(Tag.Bit256, "!plusLen").toUnique("!")
            val plus3f = TACKeyword.TMP(Tag.Bit256, "!plus3f").toUnique("!")
            val truncated = TACKeyword.TMP(Tag.Bit256, "!trunc").toUnique("!")

            val dataStart = TACKeyword.TMP(Tag.Bit256, "!dataStart").toUnique("!")

            val offsetWithinBuffer = TACKeyword.TMP(Tag.Bit256, "!offsetWithinReturn").toUnique("!")
            val stringDataAbsoluteOffset = TACKeyword.TMP(Tag.Bit256, "!absOffsetInReturn").toUnique("!")

            val dataBufferStart = TACKeyword.TMP(Tag.Bit256, "!dummyFp").toUnique("!")

            val tempVars = setOf<TACSymbol.Var>(
                bump, plus3f, truncated, dataStart, offsetWithinBuffer, stringDataAbsoluteOffset, dataBufferStart
            )
            fpWrite.ptr to CommandWithRequiredDecls(listOf(
                exp {
                    dataBufferStart `=` TACKeyword.MEM64.toVar()
                },
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = offsetWithinBuffer,
                    rhs = TACExpr.BinOp.Sub(
                        outputPointer.asSym(),
                        dataBufferStart.asSym()
                    )
                ),
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = stringDataAbsoluteOffset,
                    rhs = TACExpr.BinOp.Sub(
                        offsetWithinBuffer.asSym(),
                        28.asTACExpr /*
                         offsetWithinBuffer gives the start of the string in the returnbuffer, offset by 4. We can
                         subtract 4 to give the absolute position in the returnbuffer. Then, we need to add 32 to get
                         the start of the string *data* within the buffer. So fold that into one step, just subtract 28
                        */
                    )
                ),
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = outputPointer,
                    rhs = TACKeyword.MEM64.toVar()
                ),
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = plus3f,
                    rhs = TACExpr.Vec.Add(
                        lengthSymbol.asSym(),
                        0x3f.asTACExpr
                    )
                ),
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = truncated,
                    rhs = TACExpr.BinOp.BWAnd(
                        plus3f.asSym(),
                        MAX_EVM_UINT256.andNot(31.toBigInteger()).asTACExpr
                    )
                ),
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = bump,
                    rhs = TACExpr.Vec.Add(
                        outputPointer.asSym(),
                        truncated.asSym()
                    )
                ),
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = TACKeyword.MEM64.toVar(),
                    rhs = bump
                ),
                TACCmd.Simple.AssigningCmd.ByteStore(
                    base = TACKeyword.MEMORY.toVar(),
                    loc = outputPointer,
                    value = lengthSymbol
                ),
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = dataStart,
                    rhs = TACExpr.Vec.Add(
                        outputPointer.asSym(),
                        EVM_WORD_SIZE.asTACExpr
                    )
                ),
                TACCmd.Simple.ByteLongCopy(
                    dstBase = TACKeyword.MEMORY.toVar(),
                    dstOffset = dataStart,
                    length = lengthSymbol,
                    srcBase = TACKeyword.RETURNDATA.toVar(),
                    srcOffset = stringDataAbsoluteOffset
                )
            ), tempVars)
        }.sequential().patchForEach(c) {(where, what) ->
            this.replaceCommand(where, what)
        }
    }
}
