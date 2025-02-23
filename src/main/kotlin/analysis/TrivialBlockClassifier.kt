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

package analysis

import vc.data.TACCmd
import vc.data.TACExpr

object TrivialBlockClassifier {
    fun isTrivialBlockTo(elab: TACBlock, graph: TACCommandGraph): Boolean {
        return graph.pred(elab).size == 1 && graph.succ(elab.id).singleOrNull()?.let { nextSucc ->
            elab.commands.all { lc ->
                lc.cmd is TACCmd.Simple.NopCmd || lc.cmd is TACCmd.Simple.AnnotationCmd || lc.cmd is TACCmd.Simple.JumpdestCmd || lc.cmd is TACCmd.Simple.JumpCmd || lc.cmd is TACCmd.Simple.LabelCmd ||
                        (lc.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && lc.cmd.rhs is TACExpr.Sym.Var && run {
                            val which = graph.cache.def.defSitesOf(lc.cmd.rhs.s, lc.ptr).singleOrNull()?.takeIf {
                                graph.elab(it).maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.cmd?.rhs is TACExpr.Sym.Var
                            } ?: return@run false
                            val patt = PatternMatcher.compilePattern(graph, PatternMatcher.Pattern.FromVar { where, _ ->
                                if (where.ptr == which) {
                                    PatternMatcher.VariableMatch.Match(Unit)
                                } else {
                                    PatternMatcher.VariableMatch.Continue
                                }
                            })
                            graph.pred(nextSucc).all {
                                it == elab.id || graph.elab(it).commands.any { otherAssign ->
                                    otherAssign.cmd is TACCmd.Simple.AssigningCmd && otherAssign.cmd.lhs == lc.cmd.lhs &&
                                            patt.queryFrom(otherAssign.narrow()) is PatternMatcher.ConstLattice.Match
                                }
                            }
                        })
            }
        } == true
    }
}