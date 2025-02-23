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

package datastructures



data class GraphWithSource<V>(val graph: Graph<V>, val source: V) : Graph<V>(graph) {
    init {
        check(graph.allNodes.contains(source)) { "source must occur in graph" }
    }

    override val allNodes = graph.allNodes
    override val allEdges = graph.allEdges

    override fun toString(): String = graph.toString()


//    companion object {
//        fun <V, E> singleEdge(source: V, label: E, sink: V): GraphWithSourceAndSink<V, E> =
//            GraphWithSourceAndSink(Graph.singleEdge(source, label, sink), source, sink)
//    }
}

data class LabelledGraphWithSourceAndSink<V, E>(
    val labelledGraph: LabelledGraph<V, E>,
    val source: V,
    val sink: V
) {
    init {
        check(labelledGraph.allNodes.contains(source)) { "source must occur in graph" }
        check(labelledGraph.allNodes.contains(sink)) { "sink must occur in graph" }
    }

    override fun toString(): String = labelledGraph.toString()

    companion object {
        fun <V, E> singleEdge(source: V, label: E, sink: V): LabelledGraphWithSourceAndSink<V, E> =
            LabelledGraphWithSourceAndSink(
                LabelledGraph.singleEdge(
                    source,
                    label,
                    sink
                ), source, sink
            )

    }
}


open class LabelledGraph<V, E>(private val relation: MultiMap<V, V>, private val labelMapping: Map<Pair<V, V>, E>) :
    Graph<V>(relation) {
    open fun getEdgeLabel(src: V, tgt: V): E =
        labelMapping[src to tgt] ?: error("edge ($src, $tgt) is not present in this graph")

    override fun toString(): String =
        relation.pairs.joinToString("\n") { (src, tgt) -> "$src -(${labelMapping[src to tgt]})-> $tgt" }

    companion object {
        fun <V, E> singleEdge(source: V, label: E, sink: V): LabelledGraph<V, E> {
            val mutable = MutableLabelledGraph<V, E>()
            mutable.put(source, label, sink)
            return mutable.freeze()
        }
    }

}

class SparseLabelledGraph<V, E>(
    private val relation: MultiMap<V, V>,
    private val labelMapping: Map<Pair<V, V>, E>,
    private val defaultLabel: E
) : LabelledGraph<V, E>(relation, labelMapping) {

    operator fun get(pair: Pair<V, V>) = getEdgeLabel(pair.first, pair.second)

    override fun getEdgeLabel(src: V, tgt: V): E =
        labelMapping[src to tgt] ?: defaultLabel

}

class MutableSparseLabelledGraph<V, E>(
    private val relation: MutableMultiMap<V, V>,
    private val labelMapping: MutableMap<Pair<V, V>, E>,
    private val defaultLabel: E
) {
    constructor(defaultLabel: E) : this(
        mutableMultiMapOf<V, V>(),
        mutableMapOf<Pair<V, V>, E>(),
        defaultLabel
    )

    fun put(src: V, lab: E, tgt: V) {
        relation.add(src, tgt)
        labelMapping[src to tgt] = lab
    }

    operator fun set(pair: Pair<V, V>, label: E) = put(pair.first, label, pair.second)

    operator fun get(pair: Pair<V, V>) = getLabel(pair.first, pair.second)

    fun getLabel(src: V, tgt: V) = labelMapping[src to tgt] ?: defaultLabel

    fun freeze() = SparseLabelledGraph(relation, labelMapping, defaultLabel)

    fun getAllNonDefaultEdges(): Set<Pair<Pair<V, V>, E>> = relation.pairs
        .filter { (v1, v2) -> labelMapping[v1 to v2] != defaultLabel }
        .map { (v1, v2) -> ((v1 to v2) to labelMapping[v1 to v2]!!) }
        .toSet()
}

class MutableLabelledGraph<V, E>(
    private val relation: MutableMultiMap<V, V>,
    private val labelMapping: MutableMap<Pair<V, V>, E>
) {
    //) : LabelledGraph<V, E>(relation, labelMapping) {
    constructor() : this(mutableMultiMapOf<V, V>(), LinkedHashMap<Pair<V, V>, E>())

    operator fun set(pair: Pair<V, V>, label: E) = put(pair.first, label, pair.second)

    fun put(src: V, lab: E, tgt: V) {
        relation.add(src, tgt)
        labelMapping[src to tgt] = lab
    }

    fun freeze() = LabelledGraph(relation, labelMapping)
}

open class Graph<T>(private val relation: MultiMap<T, T>) {
    constructor(graph: Graph<T>) : this(graph.relation)

    open val allNodes
        get() =
            mutableSetOf<T>().apply {
                addAll(relation.keys)
                relation.keys.forEach { addAll(relation.getImage(it)) }
            }

    open val allEdges: Set<Pair<T, T>>
        get() = relation.pairs

    fun succs(node: T) = relation.getImage(node)
}

open class MutableGraph<T>(private val relation: MutableMultiMap<T, T>) : Graph<T>(relation) {
    constructor() : this(mutableMultiMapOf<T, T>())

    fun put(pred: T, succ: T) {
        relation.add(pred, succ)
    }
}


