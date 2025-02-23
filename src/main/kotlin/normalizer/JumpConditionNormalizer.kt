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

package normalizer

import analysis.*
import analysis.dataflow.OnDemandUseAnalysis
import parallel.*
import parallel.ParallelPool.Companion.runInherit
import utils.*
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * given
 * x = LNot y
 * jumpi x dst elseDst
 *
 * convert it to
 * jumpi y elseDst dst
 *
 * (which makes the x assignment removable later)
 */
object JumpConditionNormalizer {
    private val patternOriginal = PatternMatcher.Pattern.FromBinOp.from(
            t = TACExpr.BinRel::class.java,
            p1 = PatternMatcher.Pattern.Trivial,
            p2 = PatternMatcher.Pattern.Trivial,
            comb = { e, _, _ ->
                e
            }
    ).let { relPatt ->
        PatternMatcher.Pattern.FromBinOp.from(TACExpr.BinRel.Eq::class.java,
                p1 = relPatt,
                p2 = PatternMatcher.Pattern.FromConstant.exactly(BigInteger.ZERO),
                comb = { where, _, _ ->
                    where.enarrow<TACExpr.BinRel.Eq>()
                }
        )
    }

    private val patternTyped = PatternMatcher.Pattern.FromUnaryOp(
            extractor = { _, uexp ->
                if(uexp is TACExpr.UnaryExp.LNot) {
                    uexp.o.getAs<TACExpr.Sym>()?.s
                } else {
                    null
                }
            },
            inner = PatternMatcher.Pattern.Trivial,
            out = { where, _ ->
                where.enarrow<TACExpr.UnaryExp.LNot>()
            }
    )

    private val jumpPattern = PatternMatcher.Pattern.XOr.orSame<ExprView<TACExpr>>(
        patternOriginal,
        patternTyped
    )

    private data class Result(
            val cond: LTACCmdView<TACCmd.Simple.JumpiCmd>,
            val condVar: TACSymbol.Var,
            val invVar: TACSymbol.Var,
            val defSite: ExprView<TACExpr>
    )

    fun normalizeConditions(p: CoreTACProgram): CoreTACProgram {
        val g = p.analysisCache.graph
        val matcher = PatternMatcher.compilePattern(g, jumpPattern)
        val use = OnDemandUseAnalysis(g)
        val blocks = g.blocks
        val d = blocks.mapNotNull { block ->
            block.commands.last().takeIf { it.cmd is TACCmd.Simple.JumpiCmd && it.cmd.cond is TACSymbol.Var }
        }.forkEvery { lc ->
            Scheduler.compute {
                check(lc.cmd is TACCmd.Simple.JumpiCmd)
                matcher.query(lc.cmd.cond as TACSymbol.Var, lc).toNullableResult()?.let {
                    val condVar = it.lhs
                    val sites = use.useSitesAfter(condVar, it.ptr)
                    if(sites != setOf(lc.ptr) || lc.cmd.cond != it.lhs) {
                        null
                    } else {
                        it.exp.let { exp ->
                            Result(
                                cond = lc.narrow(),
                                condVar = it.lhs,
                                defSite = it,
                                invVar = when (exp) {
                                    is TACExpr.BinRel.Eq -> (exp.o1AsTACSymbol()) as TACSymbol.Var
                                    is TACExpr.UnaryExp.LNot -> (exp.o as TACExpr.Sym).s as TACSymbol.Var
                                    else -> error("Unexpected expression $it")
                                }
                            )
                        }
                    }
                }
            }
        }.pcompute().runInherit().filterNotNull()
        if (d.isEmpty()) {
            return p
        }
        val mut = p.toPatchingProgram()
        for(r in d) {
            if(r.condVar == r.invVar) {
                mut.update(r.defSite.ptr) {
                    TACCmd.Simple.NopCmd
                }
            }
            mut.replaceCommand(r.cond.ptr, listOf(
                r.cond.cmd.copy(
                        cond = r.invVar,
                        elseDst = r.cond.cmd.dst,
                        dst = r.cond.cmd.elseDst
                )
            ))
        }

        return mut.toCode(p)
    }
}
