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

import datastructures.stdcollections.*
import analysis.*
import analysis.worklist.StepResult
import analysis.worklist.VisitingWorklistIteration
import config.Config
import log.*
import tac.Tag
import utils.*
import vc.data.*
import vc.data.SimplePatchingProgram.Companion.patchForEach
import java.math.BigInteger
import java.util.stream.Stream

private val logger = Logger(LoggerTypes.PER_FUNCTION_SIMPLIFICATION)

/**
 * Replaces the "infamous" 'note' modifier,[] which is implemented as:
 * ```
 * modifier note {
 *         _;
 *         assembly {
 *             // log an 'anonymous' event with a constant 6 words of calldata
 *             // and four indexed topics: selector, caller, arg1 and arg2
 *             let mark := msize()                       // end of memory ensures zero
 *             mstore(0x40, add(mark, 288))              // update free memory pointer
 *             mstore(mark, 0x20)                        // bytes type data offset
 *             mstore(add(mark, 0x20), 224)              // bytes size (padded)
 *             calldatacopy(add(mark, 0x40), 0, 224)     // bytes payload
 *             log4(mark, 288,                           // calldata
 *                  shl(224, shr(224, calldataload(0))), // msg.sig
 *                  caller(),                            // msg.sender
 *                  calldataload(4),                     // arg1
 *                  calldataload(36)                     // arg2
 *                 )
 *         }
 *     }
 * ```
 *
 * This trashes the PTA. We solve this by rewriting it to operate on a fresh bytemap. We do this by finding an update
 * of the free pointer which is from an constant addition to `msize`. When then find the last statement within the same
 * block where the value that holds the read of `msize` is no longer live. This is taken to be the "end" of the msize use window.
 * We then find all "uses" of the msize value, which must be:
 * 1. writes to memory
 * 2. long copies to memory
 * 3. logs
 * 4. expressions
 *
 * If we find a use that is *not* of the above form, we abort the rewrite.
 *
 * In the 4 case, this generates new variables, to search for uses, following a pattern similar to the [analysis.alloc.FreePointerAnalysis].
 * Thus, this use search is actually a worklist. If any of these "derived from msize" variables are live outside of the
 * msize use window, we abort the rewrite.
 *
 * At the end of the above worklist, we will have found a list of variables which are derived from msize and which are
 * only used within a small window. Some of these uses affect or access memory, for these uses, we rewrite this command
 * to use a fresh bytemap (which is initialized to 0). We then erase the free pointer update.
 *
 * Q: Why can't we instrument this to use the free pointer somehow?
 * A: Because we do not faithfully model msize, and thus have no coherent value to use for `mark` in the above. If we
 * just blithely replaced `msize` with `fp`, then if this is run *after* an external function call, this will trash the
 * abi encoded values starting at the free pointer.
 */
object NoteModifierRewriter {
    private val msizePattern = PatternDSL.build {
        (Const + PatternMatcher.Pattern.AssigningPattern0(TACCmd.Simple.AssigningCmd.AssignMsizeCmd::class.java) { where, _ ->
            PatternMatcher.ConstLattice.Match(where.ptr)
        }.asBuildable()).commute.withAction { a, b -> a to b }
    }

    private data class Rewrite(
        val startLocation: CmdPointer,
        val baseMap: TACSymbol.Var,
        val rewrites: Map<CmdPointer, () -> TACCmd.Simple>
    )

    fun hasMsizeBasedFPUpdates(c: CoreTACProgram) = getMsizeBasedFPUpdates(c).findAny().isPresent

    private fun getMsizeBasedFPUpdates(c: CoreTACProgram): Stream<Pair<LTACCmdView<TACCmd.Simple.AssigningCmd>, Pair<BigInteger, CmdPointer>>> {
        val matcher = PatternMatcher.compilePattern(c.analysisCache.graph, msizePattern)
        return c.parallelLtacStream().mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd>()?.takeIf {
                it.cmd.lhs == TACKeyword.MEM64.toVar()
            }
        }.mapNotNull {
            it `to?` matcher.queryFrom(it).toNullableResult()
        }
    }

    fun transform(c: CoreTACProgram) : CoreTACProgram {
        if (!Config.RewriteMSizeAllocations.get()) {
            return c
        }
        return with(c.analysisCache.graph) {
            getMsizeBasedFPUpdates(c).mapNotNull { (update, spec) ->
                val (_, msizeRead) = spec
                val msizeSpec = elab(msizeRead).narrow<TACCmd.Simple.AssigningCmd.AssignMsizeCmd>()
                val lhs = msizeSpec.cmd.lhs
                // find the window, i.e., the point where the msize value is no longer live
                // if we can't find that within this block, abort
                val window = iterateBlock(msizeRead, excludeStart = true).takeWhile {
                    cache.lva.isLiveBefore(it.ptr, lhs)
                }.takeIf {
                    it.isNotEmpty() && !cache.lva.isLiveAfter(it.last().ptr, lhs) && it.all { lc ->
                        lc.cmd.getLhs() != lhs
                    }
                } ?: return@mapNotNull null
                val lastPoint = window.last().ptr
                // find those variables still live after the msize window closes
                val liveSet = cache.lva.liveVariablesAfter(lastPoint)
                val windowSet = window.mapToSet { it.ptr }
                /*
                 somehow the free pointer update is not in this window? This is suspicious, abort
                 */
                if(update.ptr !in windowSet) {
                    logger.info {
                        "For $msizeRead, update of free pointer $update was not in the window ending at $lastPoint"
                    }
                    return@mapNotNull null
                }
                val newBaseMap by lazy {
                    TACKeyword.TMP(Tag.ByteMap, "!msizeBuffer").toUnique("!")
                }

                /*
                 * Follow uses of the msize in variable definitions and memory accessing commands. For variable definitions, follow
                 * those uses using the same process until we find no more work to do. If we find any variables which are either
                 * 1. Used outside the window
                 * 2. Live *after* the end of the window (actually equivalent to 1)
                 * 3. Used in an unexpected way (not one of the 4 forms in the documentation of this class)
                 * We abort with a message, the right part of the `Either` return value.
                 *
                 * Otherwise, find all memory accessing/updating commands in this process and register rewrites. Return
                 * all such rewrites to be applied later, in the `Left` part of the return value.
                 */
                val rewrite = object : VisitingWorklistIteration<Pair<CmdPointer, TACSymbol.Var>, Pair<CmdPointer, () -> TACCmd.Simple>, Either<Map<CmdPointer, () -> TACCmd.Simple>, String>>() {
                    private fun err(s: () -> String) = this.halt("For msize rewrite starting at $msizeRead: ${s()}".toRight())
                    override fun process(it: Pair<CmdPointer, TACSymbol.Var>): StepResult<Pair<CmdPointer, TACSymbol.Var>, Pair<CmdPointer, () -> TACCmd.Simple>, Either<Map<CmdPointer, () -> TACCmd.Simple>, String>> {
                        val (defSite, v) = it
                        if (v in liveSet) {
                            return this.halt("Found variable $v defined at $defSite derived from msize that is live after last use of msize @ $lastPoint".toRight())
                        }
                        val uses = cache.use.useSitesAfter(v, defSite)
                        val nxt = mutableListOf<Pair<CmdPointer, TACSymbol.Var>>()
                        val rewrites = mutableListOf<Pair<CmdPointer, () -> TACCmd.Simple>>()
                        for (u in uses) {
                            if(u == update.ptr) {
                                continue
                            }
                            val useLc = elab(u)
                            if(u !in windowSet) {
                                return err { "Use of $v defined at $defSite @ $useLc is outside window ending at $lastPoint"}
                            }
                            check(u.pos > defSite.pos)
                            when (useLc.cmd) {
                                is TACCmd.Simple.AssigningCmd.AssignExpCmd -> {
                                    nxt.add(useLc.ptr to useLc.cmd.lhs)
                                }
                                is TACCmd.Simple.AssigningCmd.ByteStore -> {
                                    if(useLc.cmd.base != TACKeyword.MEMORY.toVar()) {
                                        continue
                                    }
                                    if(useLc.cmd.loc != v || useLc.cmd.value == v) {
                                        return err { "Illegal use of $v defined at $defSite @ $useLc" }
                                    }
                                    rewrites.add(useLc.ptr to {
                                        useLc.cmd.copy(base = newBaseMap)
                                    })
                                }
                                is TACCmd.Simple.ByteLongCopy -> {
                                    if(useLc.cmd.dstBase != TACKeyword.MEMORY.toVar()) {
                                        continue
                                    }
                                    if(useLc.cmd.dstOffset != v || useLc.cmd.srcOffset == v || useLc.cmd.length == v || useLc.cmd.srcBase == v) {
                                        return err { "Illegal use of $v defined at $defSite @ $useLc "}
                                    }
                                    rewrites.add(useLc.ptr to {
                                        useLc.cmd.copy(
                                            dstBase = newBaseMap
                                        )
                                    })
                                }
                                is TACCmd.Simple.LogCmd -> {
                                    if(useLc.cmd.memBaseMap != TACKeyword.MEMORY.toVar()) {
                                        continue
                                    }
                                    if(v != useLc.cmd.sourceOffset || useLc.cmd.args.withIndex().any { (i,sym) ->
                                        i != 0 && sym == v
                                        }) {
                                        return err { "Illegal use of $v defined at $defSite @ $useLc"}
                                    }
                                    rewrites.add(useLc.ptr to {
                                        useLc.cmd.copy(memBaseMap = newBaseMap)
                                    })
                                }
                                is TACCmd.Simple.SummaryCmd -> {
                                    if(useLc.cmd.summ is OpcodeSummary) {
                                        continue
                                    }
                                }
                                else -> return err {
                                    "Unknown command form $useLc for $v defined at $defSite"
                                }
                            }
                        }
                        return StepResult.Ok(
                            next = nxt,
                            result = rewrites
                        )
                    }

                    override fun reduce(results: List<Pair<CmdPointer, () -> TACCmd.Simple>>): Either<Map<CmdPointer, () -> TACCmd.Simple>, String> {
                        val ret = mutableMapOf<CmdPointer, () -> TACCmd.Simple>()
                        for ((k, r) in results) {
                            if (k in ret) {
                                return "Multiple rewrites registered for location $k".toRight()
                            }
                            ret[k] = r
                        }
                        return ret.toLeft()
                    }
                }.submit(listOf(msizeRead to lhs)).toValue({ it }, {
                    logger.info { it }
                    null
                }) ?: return@mapNotNull null
                if(update.ptr in rewrite) {
                    logger.info {
                        "Rewrites compute for $msizeRead already has rewrite at the update point $update"
                    }
                    return@mapNotNull null
                }
                Rewrite(
                    startLocation = msizeRead,
                    baseMap = newBaseMap,
                    rewrites = rewrite + (update.ptr to { -> TACCmd.Simple.NopCmd })
                )
            }.patchForEach(c, check = true) { rewrite ->
                addVarDecl(rewrite.baseMap)
                for((k, r) in rewrite.rewrites) {
                    update(k, r())
                }
                val binder = TACKeyword.TMP(Tag.Bit256, "!binder").toUnique("!")
                addVarDecl(binder)
                addBefore(rewrite.startLocation, listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = rewrite.baseMap,
                        rhs = TACExpr.MapDefinition(listOf(binder.asSym()), TACExpr.zeroExpr, tag = Tag.ByteMap)
                    )
                ))
            }
        }
    }
}
