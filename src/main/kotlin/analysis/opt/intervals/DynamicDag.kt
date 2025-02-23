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

package analysis.opt.intervals

import algorithms.getReachable
import algorithms.topologicalOrder
import com.certora.collect.*
import datastructures.*
import datastructures.stdcollections.*

/**
 * A class that efficiently maintains a DAG that can change. Currently supports on the erasure of vertices and edges.
 * Vertices that are disconnected from the roots are erased automatically.
 */
@Suppress("LocalVariableName")
class DynamicDag<@Treapable V>(_roots: Set<V>, _succs: MultiMap<V, V>) {

    private val rs = _roots.toMutableSet()
    val roots: Set<V> get() = rs

    private val vs = getReachable(rs, _succs::get).toMutableSet()
    val vertices: Set<V> get() = vs

    private val succs = mutableMultiMapOf<V, V>().apply {
        for (v in vs) {
            _succs[v]?.forEach { add(v, it) }
        }
    }
    val successors: MultiMap<V, V> get() = succs

    private val preds = reverseToMutable(succs)
    val predecessors: MultiMap<V, V> get() = preds

    /** Erases [v] and every vertex that gets disconnected as a result (unreachable from [roots]) */
    fun erase(v: V) {
        require(v in vs)
        vs -= v
        rs -= v
        for (pred in preds[v].orEmpty()) {
            succs.delete(pred, v)
        }
        preds -= v
        for (succ in succs[v].orEmpty()) {
            preds.delete(succ, v)
            if (preds[succ] == null) {
                erase(succ)
            }
        }
        succs -= v
    }

    /** disconnects the edge from [u] to [v], which may result in the erasing of disconnected vertices */
    fun disconnect(u: V, v: V) {
        succs.delete(u, v)
        preds.delete(v, u)
        if (preds[v].isNullOrEmpty()) {
            erase(v)
        }
    }

    fun topOrderSinksFirst() =
        topologicalOrder(vs, succs::get)
}
