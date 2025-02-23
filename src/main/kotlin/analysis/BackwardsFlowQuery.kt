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

import datastructures.stdcollections.*
import vc.data.TACCmd
import vc.data.TACSymbol
import java.util.*

interface SymbolQuery<T> {
    fun query(q: TACSymbol.Var, src: LTACCmd) : T
    fun queryFrom(start: LTACCmdView<TACCmd.Simple.AssigningCmd>) : T
}

abstract class BackwardsFlowQuery<T : Any>(
    val graph: TACCommandGraph,
    private val topElement: T,
    private val binaryJoin: (T, T) -> T
) : SymbolQuery<T> {

    data class Query(val symbol: TACSymbol.Var, val id: CmdPointer)

    private val resultCache = Collections.synchronizedMap(mutableMapOf<Query, T>())

    /**
     * Starting from [src] find the definition of [q], then step it's assignment (potentially issuing recursive queries)
     */
    override fun query(q : TACSymbol.Var, src: LTACCmd) : T {
        return query(Query(q, src.ptr))
    }

    /**
     * Step the assignment of [start] (potentially issuing recursive queries)
     *
     * Note that [queryFrom] and [query] are subtly different. Consider
     * x = 3
     * x := y + z
     *
     * [queryFrom] will consider the assignment on the RHS of [start] as a candidate
     * for a match, in other words, it begins matching immediately
     * "after" the assignment to x. However, [query] considers the program state "before" the assignment,
     * in other words, it begins matching at `y + z` in the above, NOT taking into consideration
     * the assignment to x.
     *
     * Thus, `(a + b).queryFrom(x := y + z)` will match, but (a + b).query(x, x := y + z)` will not.
     */
    override fun queryFrom(start: LTACCmdView<TACCmd.Simple.AssigningCmd>): T {
        return stepAssignment(start.cmd, start.ptr, setOf())
    }

    protected fun TACCmd.Simple.at(where: CmdPointer): LTACCmd = LTACCmd(where, this)

    /**
     * With the set of active queries [active], begin a query for [q] starting at [src]
     */
    protected fun query(q: TACSymbol.Var, src: CmdPointer, active: Set<Query>) = query(Query(q, src), active)

    private fun query(q: Query): T {
        if(q !in resultCache) {
            resultCache[q] = query(q, setOf())
        }
        return resultCache[q]!!
    }

    /**
     * Execute the query [q] or halt with the trivial result if this is a cycle (i.e., the query
     * appears in our [active] set)
     */
    private fun query(q: Query, active: Set<Query>) : T {
        val res = if(q in active) {
            topElement
        } else {
            step(q.id, q.symbol, active.plus(q))
        }
        resultCache.merge(q, res, binaryJoin)
        return resultCache[q]!!
    }

    /**
     * Finds the (unique) definition of [symbol] starting *before* [where], then steps that assignment (via [stepAssignment])
     * If there are multiple definitions the trivial result is returned.
     */
    private fun step(where: CmdPointer, symbol: TACSymbol.Var, active: Set<Query>): T = step(graph.elab(where), symbol, active)

    private val def = graph.cache.def
    private val dom = graph.cache.domination

    private fun step(where: LTACCmd, symbol: TACSymbol.Var, active: Set<Query>) : T {
        // find previous
        val def = def.defSitesOf(symbol, where.ptr).singleOrNull()?.takeIf {
            it.block == where.ptr.block || dom.dominates(it.block, where.ptr.block)
        } ?: return topElement

        val lc = graph.elab(def)
        check(lc.cmd is TACCmd.Simple.AssigningCmd) {
            "Wanted definition of $symbol, got $lc"
        }
        if(!filterTraversal(lc.narrow())) {
            return topElement
        }
        return stepAssignment(lc.cmd, lc.ptr, active)
    }

    /**
     * The core piece of the backwards symbol query. Assuming we're querying the definition of some symbol s
     * and it has a unique definition (given by first) [first], compute the result of the query. This may involve
     * *recursive* queries.
     */
    abstract fun stepAssignment(first: TACCmd.Simple.AssigningCmd, where: CmdPointer, active: Set<Query>): T

    open protected fun filterTraversal(l: LTACCmdView<TACCmd.Simple.AssigningCmd>) : Boolean {
        return true
    }
}
