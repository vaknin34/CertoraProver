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

package analysis.opt

import analysis.*
import datastructures.stdcollections.setOfNotNull
import tac.Tag
import vc.data.*
import java.math.BigInteger
import kotlin.collections.all
import kotlin.collections.listOf
import kotlin.collections.single
import kotlin.collections.singleOrNull

/**
 * Problematic snippet:
A = M[0x80] (2) // originally wrote a boolean there (e.g. true)
B = A==0x0 (false) // cast to bool
C = (LNot(B:bool) ? 0x1 : 0x0) (1) // recast back to bv256
B2 = A==C (false) // oops, this should be true!
 *
 * match a comparison where C is the result of A being converted to bool and then back to integer.
 * If A is only used in a comparison to 0, or in B2's definition, then assign true to B2.
 *
 * This can happen even if we scalarized the calldata because it can take any value.
 */
object BoolComparisonFixer {
    private val maybeNegatedBoolPattern = PatternMatcher.Pattern.FromUnaryOp(
            extractor = { _, u ->
                ((u as? TACExpr.UnaryExp.LNot)?.o as? TACExpr.Sym.Var)?.s
            },
            inner = PatternDSL.build {
                (Var `==` Const(BigInteger.ZERO)).withAction { vv, _ -> PatternMatcher.VariableMatch.Match(vv) }
            },
            out = { _, maybeBool -> maybeBool }
    )

    private val castedBoolToIntVar = PatternMatcher.Pattern.Ite(
            maybeNegatedBoolPattern,
            PatternMatcher.Pattern.FromConstant.exactly(BigInteger.ONE),
            PatternMatcher.Pattern.FromConstant.exactly(BigInteger.ZERO),
            { _, i, _, _ -> i }
    ).asBuildable().toBuilder()

    private data class PotentialBoolComparison(
            val where: CmdPointer,
            val potentialBoolVar: TACSymbol.Var
    )

    private val pattern = PatternDSL.build {
        (Var `==` castedBoolToIntVar).commute.withAction { lcmd, v, matchCasted ->
            if (v == matchCasted.data) {
                PotentialBoolComparison(lcmd.ptr, v)
            } else {
                null
            }
        }
    }

    /**
     * pattern matcher does not support nested expressions, so we unnest the LNots as ITE conditions ("i"s)
     */
    private fun unnestLNotInsideIte(prog: CoreTACProgram): CoreTACProgram {
        val graph = prog.analysisCache.graph
        val patching = prog.toPatchingProgram()
        graph.commands.forEach { lcmd ->
            val assign = lcmd.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()
            val ite = assign?.cmd?.rhs as? TACExpr.TernaryExp.Ite
            if (ite != null && ite.i is TACExpr.UnaryExp.LNot) {
                val tmp = TACKeyword.TMP(Tag.Bool, "unnest")
                patching.replaceCommand(lcmd.ptr,
                        listOf(
                                TACCmd.Simple.AssigningCmd.AssignExpCmd(tmp, ite.i),
                                assign.cmd.copy(rhs = ite.copy(i = tmp.asSym()))
                        )
                )
                patching.addVarDecl(tmp)
            }
        }
        return patching.toCode(prog)
    }

    fun fix(prog_: CoreTACProgram): CoreTACProgram {
        val prog = unnestLNotInsideIte(prog_)
        val graph = prog.analysisCache.graph
        val def = prog.analysisCache.def
        val use = prog.analysisCache.use
        val matcher = PatternMatcher.compilePattern(graph, pattern)

        val patching = prog.toPatchingProgram()

        graph.commands.forEach { lcmd ->
            val cond = lcmd.maybeNarrow<TACCmd.Simple.JumpiCmd>()?.cmd?.cond as? TACSymbol.Var
            if (cond != null) {
                matcher.query(cond, lcmd).toNullableResult()?.let { potentialBoolComparison ->
                    // find def of potential bool var
                    // (single or 0 defs)
                    val defs = def.defSitesOf(potentialBoolComparison.potentialBoolVar, potentialBoolComparison.where)
                    // if 0 defs, it's a havoc'd variable. Check all uses from root
                    val defSite = defs.singleOrNull() ?: graph.roots.single().ptr
                    // find uses
                    val uses = use.useSitesAfter(potentialBoolComparison.potentialBoolVar, defSite)
                    // all uses are either as part of `x == 0` or the command where we compare
                    uses.all { p ->
                        p == potentialBoolComparison.where || (graph.elab(p).maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.cmd?.rhs?.let { exp ->
                            exp as? TACExpr.BinRel.Eq
                        }?.let { exp ->
                            setOfNotNull(exp.o1AsNullableTACSymbol(), exp.o2AsNullableTACSymbol()).let { s ->
                                TACSymbol.lift(0) in s && potentialBoolComparison.potentialBoolVar in s
                            }
                        }) == true || graph.elab(p).cmd is TACCmd.Simple.AnnotationCmd
                    }.let { toReplace ->
                        if (toReplace) {
                            patching.update(potentialBoolComparison.where) { TACCmd.Simple.AssigningCmd.AssignExpCmd(cond, TACSymbol.True) }
                        }
                    }
                }
            }

        }

        return patching.toCode(prog)
    }
}
