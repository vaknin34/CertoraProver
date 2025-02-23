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

import analysis.dataflow.IDefAnalysis
import datastructures.ArrayHashMap
import datastructures.ArrayHashSet
import datastructures.stdcollections.*
import tac.CallId
import tac.NBId
import vc.data.*
import java.util.*

/**
 * An extension of [IDefAnalysis] that automatically skips single-line definitions such as:
 * p1: x1 := x0
 * p2: x2 := x1
 * p3: x3 := x2
 * such that defOf(x2, p3) = {p1} rather than {p2}
 */
open class NonTrivialDefAnalysis(val graph: TACCommandGraph, private val def: IDefAnalysis = graph.cache.def) {
    /**
    Returns a single [LTACCmd] defining [v] in [ptr], or null if it's either not existing, not single, or not of type @param T.
     */
    inline fun <reified T : TACCmd.Simple.AssigningCmd> getDefCmd(v: TACSymbol.Var, ptr: CmdPointer, noinline stopAt: ((TACSymbol.Var) -> Boolean)? = defaultStopAt) =
        nontrivialDefSingleOrNull(v, ptr, stopAt)?.let { res ->
            graph.elab(res).cmd.takeIf { it is T }?.let { LTACCmd(res, it as T).narrow<T>() }
        }

    /**
    Returns a single [TACExpr] that is the definition of [v] in [ptr], or null if it's either not existing, not single, or not of type @param T.
     */
    inline fun <reified T : TACExpr> getDefAsExpr(v: TACSymbol.Var, ptr: CmdPointer, noinline stopAt: ((TACSymbol.Var) -> Boolean)? = defaultStopAt) =
        getDefCmd<TACCmd.Simple.AssigningCmd.AssignExpCmd>(v, ptr, stopAt)?.let {
            if (it.cmd.rhs !is T) {
                null
            } else {
                it.wrapped.enarrow<T>()
            }
        }


    /**
    Like [getDefAsExpr] but will stop when seeing the M0x40 special variable: [TACKeyword.MEM64]
     */
    inline fun <reified T : TACExpr> getDefAsExprIgnoreM0x40(
        v: TACSymbol.Var,
        ptr: CmdPointer,
        callId: CallId,
        noinline stopAt: ((TACSymbol.Var) -> Boolean)? = defaultStopAt
    ) =
        nontrivialDefSingleOrNull(v, ptr) {
            it == TACKeyword.MEM64.toVar(callId) || stopAt != null && stopAt(it)
        }?.let { res ->
            graph.elab(res).cmd.takeIf { it is TACCmd.Simple.AssigningCmd.AssignExpCmd }?.let { cmd ->
                if ((cmd as TACCmd.Simple.AssigningCmd.AssignExpCmd).rhs !is T) {
                    null
                } else {
                    LTACCmd(res, cmd).enarrow<T>()
                }
            }
        }

    fun nontrivialDef(src: TACSymbol.Var, origin: LTACCmd): Set<CmdPointer> {
        return this.nontrivialDef(src, origin.ptr)
    }

    fun nontrivialDefSingleOrNull(src: TACSymbol.Var, origin: LTACCmd): CmdPointer? {
        return this.nontrivialDefSingleOrNull(src, origin.ptr, defaultStopAt)
    }

    open val defaultStopAt: ((TACSymbol.Var) -> Boolean)? get() = null

    /**
     * Get the set of [CmdPointer]s that contain definitions of variable [src] in [origin] pointer,
     *   and if [stopAt] is given, stopping if it sees a definition satisfying [stopAt]
     */
    fun nontrivialDefSequence(src: TACSymbol.Var, origin: CmdPointer, stopAt: ((TACSymbol.Var) -> Boolean)?) = sequence<CmdPointer> {
        val visited = ArrayHashMap<TACSymbol.Var, MutableSet<CmdPointer>>()
        val vl = ArrayDeque<TACSymbol.Var>()
        val pl = ArrayDeque<CmdPointer>()
        vl.push(src)
        pl.push(origin)
        while (vl.isNotEmpty()) {
            val v = vl.pop()
            val p = pl.pop()

            if (visited.getOrPut(v) { ArrayHashSet() }.add(p)) {
                val sites = def.defSitesOf(v, p)
                if (sites.isEmpty()) {
                    if (p != origin) {
                        yield(p)
                    }
                } else {
                    // if there are multiple sites, this may break soundness in certain cases
                    if (isSingleDefSites && sites.size > 1) {
                        // if we return here we would return an empty sequence.
                        // while technically the return command would return whatever was yielded already, in this case,
                        // nothing will be yielded---In every iteration we push at most one element to the deques,
                        // as we are considering at most one def site.
                        // For that element we pushed, if we find another single defsite, we again may either yield (without pushing any extra elements), or push it.
                        // and if there are multiple def sites we just return with nothing yielded.
                        return@sequence
                    }
                    sites.forEach { s ->
                        if (transition(p, s)) {
                            val cmd = graph.toCommand(s)
                            assert(cmd is TACCmd.Simple.AssigningCmd && cmd.lhs == v)
                            if (cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && cmd.rhs is TACExpr.Sym.Var && (stopAt == null || !stopAt(cmd.rhs.s))) {
                                vl.push(cmd.rhs.s)
                                pl.push(s)
                            } else {
                                yield(s)
                            }
                        }
                    }
                }
            }
        }
    }

    fun nontrivialDef(src: TACSymbol.Var, origin: CmdPointer, stopAt: TACSymbol.Var): Set<CmdPointer> =
        nontrivialDefSequence(src, origin) { it == stopAt }.toSet()

    fun nontrivialDef(src: TACSymbol.Var, origin: CmdPointer): Set<CmdPointer> =
        nontrivialDefSequence(src, origin, defaultStopAt).toSet()

    fun nontrivialDefSingleOrNull(src: TACSymbol.Var, origin: CmdPointer, stopAt: ((TACSymbol.Var) -> Boolean)?): CmdPointer? =
        nontrivialDefSequence(src, origin, stopAt).singleOrNull()

    fun nontrivialDefSingleOrNull(src: TACSymbol.Var, origin: CmdPointer, stopAt: TACSymbol.Var): CmdPointer? =
        nontrivialDefSequence(src, origin) { it == stopAt }.singleOrNull()

    fun nontrivialDefSingleOrNull(src: TACSymbol.Var, origin: CmdPointer): CmdPointer? =
        nontrivialDefSequence(src, origin, defaultStopAt).singleOrNull()

    protected open fun transition(from: CmdPointer, to: CmdPointer): Boolean {
        return true
    }

    // if true, will only allow a single def site in every iteration inside nontrivialDefSequence, otherwise will return an empty sequence
    protected open val isSingleDefSites: Boolean = false
}

open class ScopedNonTrivialDefAnalysis(
    private val scope: Set<NBId>,
    graph: TACCommandGraph,
    val def: IDefAnalysis = graph.cache.def
) : NonTrivialDefAnalysis(graph, def) {
    override fun transition(from: CmdPointer, to: CmdPointer): Boolean =
        to.block in scope

}
