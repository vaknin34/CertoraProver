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
import analysis.alloc.AllocationAnalysis.compilePatternDirectFPReadsOnly
import analysis.alloc.AllocationAnalysis.roundUp
import analysis.loop.LoopInterpolation
import evm.EVM_WORD_SIZE
import kotlin.streams.*
import log.*
import tac.NBId
import utils.*
import vc.data.*
import vc.data.SimplePatchingProgram.Companion.patchForEach
import vc.data.tacexprutil.*

private val logger = Logger(LoggerTypes.ALLOC)

/**
    Finds FP writes that look like `fp = fp + roundUp(x - fp)`, where `x` is known to equal `fp + 0x20 + sz * n`
    (according to the instrumentation from [LoopInterpolation]), and rewrites them to `fp = fp + roundUp(0x20 + sz*n)`,
    so that [AllocationAnalysis] can recognize the allocation pattern.
 */
object LoopInterpolationAllocationRewriter {

    private fun interBlockBackwardsFrom(g: TACCommandGraph, x: CmdPointer) : Sequence<LTACCmd> {
        val blockGenerator = sequence<NBId> {
            var currBlock : NBId? = x.block
            while(currBlock != null) {
                yield(currBlock)
                currBlock = g.pred(currBlock).singleOrNull()
            }
        }.asIterable()
        return sequence {
            var started = false
            for(lc in g.lcmdSequence(blockGenerator, reverse = true)) {
                if(started) {
                    yield(lc)
                }
                started = started || lc.ptr == x
            }
        }
    }

    data class SubtractionMatch(
        val subtractionLoc: CmdPointer,
        val fpVar: TACSymbol.Var,
        val xLoc: CmdPointer,
        val xVar: TACSymbol.Var
    )

    fun rewrite(code: CoreTACProgram): CoreTACProgram {
        val graph = code.analysisCache.graph
        val nonTrivialDefAnalysis = NonTrivialDefAnalysis(graph, graph.cache.def)
        val gvn = graph.cache.gvn

        logger.trace {
            "In ${code.name}: looking for allocation pattern `fp=fp+roundUp(x-fp)`"
        }

        // matches `v` if `v` equals the value of `fp` at `fpLoc`
        fun matchFp(v: TACSymbol.Var, vLoc: CmdPointer, fpLoc: CmdPointer) =
            if (v in gvn.findCopiesAt(vLoc, fpLoc to TACKeyword.MEM64.toVar())) {
                PatternMatcher.VariableMatch.Match(v)
            } else {
                PatternMatcher.VariableMatch.NoMatch
            }

        val matchSubtract32 = PatternMatcher.compilePattern(graph, PatternDSL.build {
            ((PatternMatcher.Pattern.AnySymbol.anySymbol.asBuildable() - PatternMatcher.Pattern.AnySymbol.anySymbol.asBuildable()).withAction { where, _, _ ->
                where
            } - EVM_WORD_SIZE()).first
        })

        // Look for `fp = fpCopy + roundUp(x - fp)`, and return `fpCopy` and `x`
        val alloc = PatternMatcher.compilePatternDirectFPReadsOnly(
            graph,
            PatternDSL.build {
                (
                    Var { v, loc ->
                        matchFp(v, loc.ptr, loc.ptr)
                    } + roundUp {
                        (Var.withLocation - Var { v, loc -> matchFp(v, loc.ptr, loc.ptr) }).withAction { ltacCmd, pair, _ ->
                            ltacCmd.ptr to pair
                        }
                    }
                ).commute.withAction { fpVar, (subtractLoc, xPair) ->
                    SubtractionMatch(subtractLoc, fpVar, xPair.first, xPair.second)
                }
            }
        )
        val replacements = code.parallelLtacStream().mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd>()?.takeIf { it.cmd.lhs == TACKeyword.MEM64.toVar() }
        }.mapNotNull { lcmd ->
            logger.trace {
                "In ${code.name} at $lcmd.ptr: checking for `fp=fp+roundUp(x-fp)`"
            }

            val (subLoc, fpVar, xLoc, xVar) = alloc.queryFrom(lcmd).toNullableResult() ?: return@mapNotNull null

            logger.trace {
                "In ${code.name} at $lcmd.ptr: found `fp=fp+roundUp($xVar-fp)`"
            }

            // Now look for `assume x == fp + 0x20 + sz * n`
            val assume = PatternMatcher.compilePatternDirectFPReadsOnly(
                graph,
                PatternDSL.build {
                    (!xVar `==` commuteThree(
                        Var { v, loc -> matchFp(v, loc.ptr, lcmd.ptr) },
                        0x20(),
                        (Const * Var).commute.toBuilder(),
                        PatternDSL.CommutativeCombinator.add
                    ) { _, _, params -> params }).commute.second
                }
            )
            graph.blockCmdsBackwardFrom(xLoc).mapNotNull {
                ((it.cmd as? TACCmd.Simple.AssumeCmd)?.cond as? TACSymbol.Var)?.let { v ->
                    assume.query(v, it).toNullableResult()
                }
            }.singleOrNull()?.takeIf { (sz, _) ->
                // make sure this array is not a bytes array allocation
                sz != EVM_WORD_SIZE || interBlockBackwardsFrom(graph, lcmd.ptr).takeWhile {
                    it.cmd.getLhs() != TACKeyword.MEM64.toVar() &&
                        it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.cmd?.rhs?.equivSym(TACKeyword.MEM64) != true
                }.firstNotNullOfOrNull {
                    it.maybeNarrow<TACCmd.Simple.AssigningCmd.ByteStore>()
                }?.takeIf { penultimateWrite ->
                    (penultimateWrite.cmd.loc as? TACSymbol.Var)?.let { locVar ->
                        locVar in gvn.findCopiesAt(penultimateWrite.ptr, source = lcmd.ptr to TACKeyword.MEM64.toVar())
                    } == true
                }?.let { lengthWrite ->
                    val lenValue = lengthWrite.cmd.value as? TACSymbol.Var ?: return@takeIf true
                    matchSubtract32.query(lenValue, lengthWrite.wrapped).toNullableResult()?.ptr ?: return@takeIf true
                } != subLoc
            }?.let { (sz, n) ->
                // Replace with `fp = fp + roundUp(0x20 + sz*n)`

                // Find the original def of the length, so that the init analysis can find the length assignment.
                val nDef = nonTrivialDefAnalysis.nontrivialDefSingleOrNull(n, lcmd.ptr)
                    ?.let(graph::elab)?.maybeNarrow<TACCmd.Simple.AssigningCmd>()?.cmd?.lhs
                    ?: return@mapNotNull null

                logger.debug {
                    "In ${code.name} at $lcmd.ptr: replacing `fp=fp+roundUp($xVar-fp)` with `fp=fp+roundUp(0x20+$sz*$nDef)`"
                }
                lcmd.ptr to ExprUnfolder.unfoldTo(
                    TACExprFactUntyped {
                        fpVar.asSym() add (
                            (
                                0x20.asTACExpr add (sz.asTACExpr mul nDef.asSym()) add 0x1f.asTACExpr
                            ) bwAnd lower32BitMask.asTACExpr
                        )
                    },
                    TACKeyword.MEM64.toVar()
                )
            }
        }

        return replacements.patchForEach(code) { (ptr, replacement) ->
            replaceCommand(ptr, replacement)
        }
    }
}
