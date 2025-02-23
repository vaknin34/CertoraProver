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

package analysis.loop

import analysis.*
import utils.*
import vc.data.*
import vc.data.tacexprutil.TACExprFreeVarsCollector
import vc.data.tacexprutil.TACExprUtils
import java.math.BigInteger
import java.util.stream.Collectors

object SimpleLoopSummarization {
    /**
     * For a loop [l], return a map of variables mutated in the loop to an expression that defines
     * how they are mutated in a single iteration of the loop. e.g.:
     *
     * while(*) {
     *   t = x + 1
     *   x = t
     * }
     *
     * gives `{x => x + 1}`
     */
    fun summarizeLoop(g: TACCommandGraph, l: Loop) : Map<TACSymbol.Var, TACExpr> {
        val nonTrivialDef = ScopedNonTrivialDefAnalysis(
                scope = l.body,
                graph = g,
                def = g.cache.def
        )
        val head = g.elab(l.head).commands.first().ptr
        val liveAtHead = g.cache.lva.liveVariablesBefore(head)
        return l.body.parallelStream().flatMap {
            g.elab(it).commands.stream()
        }.mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd>()?.cmd?.lhs
        }.filter {
            it in liveAtHead
        }.sequential().distinct().parallel().mapNotNull {
            val src = nonTrivialDef.nontrivialDefSingleOrNull(it, head)?.let(g::elab)?.narrow<TACCmd.Simple.AssigningCmd>() ?: return@mapNotNull null
            it `to?` search(g, mutableSetOf(), nonTrivialDef, where = src, src = src)
        }.map { (k, e) ->
            k to (canonicalizeTerm(l, graph = g, e)?.let {
                if(it.e == null) {
                    it.k.asTACExpr
                } else if(it.k != BigInteger.ZERO) {
                    TACExpr.Vec.Add(it.e, it.k.asTACExpr)
                } else {
                    it.e
                }
            } ?: e)
        }.collect(Collectors.toList()).toMap()
    }

    /**
     * "Canonicalize" an addition term, changing, e.g. (v1 + (v2 + 4) + 6) into (v1 + v2) + 10.
     *
     * [e], if non-null are symbolic terms of the addition, expected to be from the grammar:
     *
     * e ::=
     *    e + e
     *    | v
     *
     * [k] is the numeric component. NB this is not _really_ a canonicalization because it doesn't treat
     * e = (v1 + v2) as equivalent to e = (v2 + v1)
     */
    private data class TermAccumulator(val e: TACExpr?, val k: BigInteger)

    private fun canonicalizeTerm(l: Loop, graph: TACCommandGraph, e: TACExpr) : TermAccumulator? {
        return when(e) {
            is TACExpr.Vec.Add -> {
                canonicalizeTerm(l = l, graph = graph, e.o1)?.let { t1 ->
                    canonicalizeTerm(l = l, graph = graph, e.o2)?.let { t2 ->
                        val eNext = if(t2.e != null && t1.e != null) {
                            TACExpr.Vec.Add(t1.e, t2.e)
                        } else {
                            t1.e ?: t2.e
                        }
                        val kNext = t1.k + t2.k
                        TermAccumulator(
                            eNext, kNext
                        )
                    }
                }
            }
            is TACExpr.Sym.Const -> TermAccumulator(null, e.s.value)
            is TACExpr.Sym.Var -> {
                val mca = MustBeConstantAnalysis(
                    graph = graph,
                    wrapped = NonTrivialDefAnalysis(graph)
                )
                val vK = mca.mustBeConstantAt(graph.elab(l.head).commands.first().ptr, e.s) ?: return TermAccumulator(
                    k = BigInteger.ZERO,
                    e = e
                )
                /**
                 * Is this variable constant at the head of the loop and not mutated within the loop?
                 */
                return if(l.body.parallelStream().flatMap {
                        graph.elab(it).commands.stream()
                    }.noneMatch {
                        it.cmd.getLhs() == e.s
                    }) {
                    TermAccumulator(e = null, k = vK)
                } else {
                    TermAccumulator(e = e, BigInteger.ZERO)
                }
            }
            else -> null
        }
    }

    private fun search(
            g: TACCommandGraph,
            visited: MutableSet<CmdPointer>,
            scoped: NonTrivialDefAnalysis,
            where: LTACCmdView<TACCmd.Simple.AssigningCmd>,
            src: LTACCmdView<TACCmd.Simple.AssigningCmd>
    ) : TACExpr? {
        val c = (where.cmd as? TACCmd.Simple.AssigningCmd.AssignExpCmd) ?: return null
        val fv = TACExprFreeVarsCollector.getFreeVars(c.rhs)
        return fv.monadicMap {
            val nd = scoped.nontrivialDef(it, where.ptr)
            if(nd.isEmpty() || nd.size == 1 && nd.first() == src.ptr) {
                (it.asSym() to it.asSym())
            } else if(nd.size > 1 || nd.first() in visited) {
                null
            } else {
                val w = g.elab(nd.first()).narrow<TACCmd.Simple.AssigningCmd>()
                visited.add(nd.first())
                val toRet = search(g, visited, scoped, w, src)
                visited.remove(nd.first())
                it.asSym() `to?` toRet
            }
        }?.let {
            TACExprUtils.SubstitutorVar(it.toMap()).transformOuter(c.rhs)
        }
    }
}