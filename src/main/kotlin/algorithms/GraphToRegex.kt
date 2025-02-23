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

package algorithms

import algorithms.AssociativityRequirement.DONT_FORCE
import algorithms.AssociativityRequirement.FORCE_TIMES_RIGHTASSOCIATIVE
import algorithms.Regex.Empty
import datastructures.Graph
import datastructures.GraphWithSource
import datastructures.LabelledGraphWithSourceAndSink
import datastructures.MutableSparseLabelledGraph


/**
 * @param L regex letter
 */
class RegexOps<L>(
    val plus: (List<L>) -> L,
    val times: (List<L>) -> L,
    val star: (L) -> L,
    val associativityRequirement: AssociativityRequirement
) {
    /**
     * Replaces all the operators in [re] with their analogue among [plus], [times], [star], and applies the
     * new operators to reduce the [Regex]<L> to just an object of type [L].
     */
    fun reduceRegex(re: Regex<L>): L = when (re) {
        is Empty ->
            throw UnsupportedOperationException("reduceRegex $re should probably remove this beforehand")
        is Regex.Plus -> plus(re.ops.map { reduceRegex(it) })
        is Regex.Times -> {
            when (associativityRequirement) {
                FORCE_TIMES_RIGHTASSOCIATIVE -> {
                    val opsMapped = re.ops.asReversed().map { reduceRegex(it) }.asReversed()
                    times(opsMapped)
                }
                DONT_FORCE -> {
                    times(re.ops.map { reduceRegex(it) })
                }
            }
        }
        is Regex.Star -> star(reduceRegex(re.op))
        is Regex.LetterOrEpsilon.Epsilon ->
            throw UnsupportedOperationException("reduceRegex $re should probably make whole thing epsilon-free")
        is Regex.LetterOrEpsilon.Letter -> re.letter
    }
}

sealed class Regex<L> {

    class Empty<L> private constructor() : Regex<L>() {
        override fun toString(): String = "empty"

        companion object {
            /** Looks weird, is designed to be a way out of the "generics vs objects" dilemma.
             * All generic instances share the same Empty object -- I'm not sure if it's better or worse than the
             * "hashCode() = 0  solution we had before...
             */
            private val instance = Empty<Any>()

            @Suppress("UNCHECKED_CAST")
            operator fun <L> invoke(): Empty<L> = instance as Empty<L>
        }
    }

    sealed class LetterOrEpsilon<L> : Regex<L>() {
        class Epsilon<L> : Regex<L>() {
            override fun toString(): String = "eps"//utils.epsilon

            companion object {
                /** see [Empty] */
                private val instance = Epsilon<Any>()

                @Suppress("UNCHECKED_CAST")
                operator fun <L> invoke(): Epsilon<L> = instance as Epsilon<L>
            }
        }

        data class Letter<L>(val letter: L) : Regex<L>() {
            override fun toString(): String = letter.toString()
            override fun hashCode(): Int = letter.hashCode()
            override fun equals(other: Any?): Boolean = other is Letter<*> && letter == other.letter
        }
    }

    data class Plus<L> private constructor(val ops: List<Regex<L>>) : Regex<L>() {
        override fun toString(): String = "(${ops.joinToString(" + ")})"

        companion object {
            operator fun <L> invoke(op1: Regex<L>, op2: Regex<L>): Regex<L> = invoke(listOf(op1, op2))
            operator fun <L> invoke(ops: List<Regex<L>>): Regex<L> =
                when (ops.size) {
                    0 -> getEmpty()
                    1 -> ops[0]
                    else -> Plus(ops)
                }

            operator fun <L> invoke(vararg ops: Regex<L>): Regex<L> = Plus(ops.toList())
        }
    }

    data class Times<L> private constructor(val ops: List<Regex<L>>) : Regex<L>() {
        override fun toString(): String = "(${ops.joinToString(" . ")})"

        companion object {
            operator fun <L> invoke(op1: Regex<L>, op2: Regex<L>): Regex<L> = invoke(listOf(op1, op2))
            operator fun <L> invoke(ops: List<Regex<L>>): Regex<L> =
                when (ops.size) {
                    0 -> getEpsilon()
                    1 -> ops[0]
                    else -> Times(ops)
                }

            operator fun <L> invoke(vararg ops: Regex<L>): Regex<L> = Times(ops.toList())
        }
    }


    data class Star<L>(val op: Regex<L>) : Regex<L>() {
        override fun toString(): String = "$op*"
    }

    fun star(): Regex<L> = Star(this)

    operator fun plus(other: Regex<L>): Regex<L> =
        Plus(this, other)

    operator fun times(other: Regex<L>): Regex<L> =
        Times(this, other)


    fun <M> transformLetters(letterTransformer: (L) -> Regex<M>): Regex<M> = when (this) {
        is Empty -> Empty()
        is LetterOrEpsilon.Epsilon -> LetterOrEpsilon.Epsilon()
        is LetterOrEpsilon.Letter -> letterTransformer(this.letter)
        is Plus -> Plus(ops.map { it.transformLetters(letterTransformer) })
        is Times -> Times(ops.map { it.transformLetters(letterTransformer) })
        is Star -> Star(op.transformLetters(letterTransformer))
    }

    fun transformPost(transformer: (Regex<L>) -> Regex<L>): Regex<L> = transformer(
        when (this) {
            is Empty -> this
            is LetterOrEpsilon.Epsilon -> this
            is LetterOrEpsilon.Letter -> this
            is Plus -> Plus(ops.map { it.transformPost(transformer) })
            is Times -> Times(ops.map { it.transformPost(transformer) })
            is Star -> Star(op.transformPost(transformer))
        }
    )

    companion object {

        fun <L> getEmpty(): Regex<L> = Empty()

        fun <L> getEpsilon(): Regex<L> =
            LetterOrEpsilon.Epsilon()
    }

}


/**
 * This enum represents an associativity requirement for [Regexes].
 *
 * Background:
 * Some [TACSummary] computations, in particular [ComputeTACSummaryProjectAndPrune] require the application of
 * [ComputeTACSummary.sequentialComposition] to happen starting from the sink(s) of the program and progressing to the
 * source.
 * We force this ordering by specifying an requirement for the associativity when building [Regex]s in this file's
 * methods.
 *
 */
enum class AssociativityRequirement {
    DONT_FORCE,

    /** enforce that concatenated "times" operation, i.e. iterated sequential composition, is represented as a
     * right-associative regex */
    FORCE_TIMES_RIGHTASSOCIATIVE
}


private typealias Edge<N> = Pair<N, N>

private data class PathExpression<N>(val regex: Regex<Edge<N>>, val src: N, val tgt: N)
private data class PathSequence<N>(private val sequence: List<PathExpression<N>>) : List<PathExpression<N>> by sequence


/**
 * Converts a [graph] with a marked [source] and [sink] to a regular expression (letters are the edges of the graph) that
 * denotes all the paths from [source] to [sink] in [graph].
 *
 * Implements an algorithm by Tarjan (1981, or 1979, depending on the version) to compute a regular expression from a
 * graph that represents the graph's  paths (aka. a "path expression").
 *  "Tarjan, R.E., Fast Algorithms for Solving Path Problems, Stanford University, 1979"
 */
class GraphToRegex<N>(
    val graph: Graph<N>,
    val source: N,
    val sink: N,
    val associativityRequirement: AssociativityRequirement
) {
    val result: Regex<Edge<N>> = computeResult()

    private fun computeResult(): Regex<Edge<N>> {
        //TODO: use a smarter ordering here somehow?? deterministic would be nice, too...
        val ordering: Ordering<N> = Ordering(graph.allNodes.mapIndexed { index, node -> node to index }.toMap())
        val pathSequence = eliminate(GraphWithSource(graph, source), ordering)
        return solve(pathSequence, source)[sink] ?: error("should not happen")
    }

    /** Probably-less-than-elegant implementation of an order on an arbirary set of elements. */
    class Ordering<E>(private val elementToIndex: Map<E, Int>) : Comparator<E> {
        fun getElementsStrictlyGreaterThan(e: E): List<E> =
            (elementToIndex[e] ?: error("element $e does not appear in this ordering")).let { indexOfE ->
                elementToIndex.entries.filter { en -> en.value > indexOfE }
                    .map { it.key }
            }

        fun isSmallerOrEqual(l: E, r: E): Boolean =
            elementToIndex[l] ?: error("element $l does not appear in this ordering") <=
                    elementToIndex[r] ?: error("element $r does not appear in this ordering")

        fun isStrictlyGreater(l: E, r: E): Boolean = !isSmallerOrEqual(l, r)

        override fun compare(l: E, r: E): Int =
            (elementToIndex[l] ?: error("element $l does not appear in this ordering")) - (elementToIndex[r]
                ?: error("element $r does not appear in this ordering"))
    }

    /**
     * @param graph the input graph that is to be converted to a [Regex]
     * @param ordering ordering of the graph nodes (this ordering can be crucial for performance..)
     * @param startNode designates a node of the graph as the source/start node
     */
    private fun eliminate(
        graph: GraphWithSource<N>, ordering: Ordering<N>
    ): PathSequence<N> {
        val P: MutableSparseLabelledGraph<N, Regex<Edge<N>>> =
            MutableSparseLabelledGraph(Regex.getEmpty())

        val startNode = graph.source

        P[startNode to startNode] = Regex.getEpsilon()
        graph.allEdges.forEach { (src, tgt) ->
            P[src to tgt] = simplify(P[src to tgt] + Regex.LetterOrEpsilon.Letter(src to tgt))
        }

        // eliminate
        graph.allNodes.forEach { v ->
            P[v to v] = simplify(P[v to v].star())

            ordering.getElementsStrictlyGreaterThan(v)
                .filter { P[it to v] != Empty<Edge<N>>() }
                .forEach { u ->
                    P[u to v] = simplify(P[u to v] * P[v to v])
                    ordering.getElementsStrictlyGreaterThan(v)
                        .filter { P[v to it] != Empty<Edge<N>>() }
                        .forEach { w ->
                            P[u to w] = simplify(P[u to w] + simplify(P[u to v] * P[v to w]))
                        }
                }
        }

        val ascending = P.getAllNonDefaultEdges()
            .filter { (pair, re) ->
                val u = pair.first
                val w = pair.second
//                re !is Empty &&
                re !is Regex.LetterOrEpsilon.Epsilon && ordering.isSmallerOrEqual(u, w)
            }.map { (pair, re) ->
                val u = pair.first
                val w = pair.second
                PathExpression(re, u, w)
            }.sortedWith(Comparator { t1: PathExpression<N>, t2: PathExpression<N> ->
                ordering.compare(t1.src, t2.src)
            })
        val descending = P.getAllNonDefaultEdges()
            .filter { (pair, _) ->
                val u = pair.first
                val w = pair.second
                ordering.isStrictlyGreater(u, w)
            }.map { (pair, re) ->
                val u = pair.first
                val w = pair.second
                PathExpression(re, u, w)
            }.sortedWith(Comparator { t1: PathExpression<N>, t2: PathExpression<N> ->
                ordering.compare(t2.src, t1.src)
            })
        return PathSequence(ascending + descending)
    }

    private fun solve(
        pathSequence: PathSequence<N>,
        startNode: N
    ): Map<N, Regex<Edge<N>>> {
        val P: MutableSparseLabelledGraph<N, Regex<Pair<N, N>>> =
            MutableSparseLabelledGraph(Regex.getEmpty())

        P[startNode to startNode] = Regex.getEpsilon()

        pathSequence.forEach { (re, v, w) ->
            if (v == w)
                P[startNode to v] =
                    simplify(
                        P[startNode to v] * re
                    )
            else
                P[startNode to w] =
                    simplify(
                        simplify(
                            P[startNode to w] +
                                    simplify(
                                        P[startNode to v] * re
                                    )
                        )
                    )
        }
        val frozen = P.freeze()
        return frozen.allNodes.map { tgt -> Pair(tgt, frozen[startNode to tgt]) }.toMap()
    }

    private fun simplify(re: Regex<Edge<N>>): Regex<Edge<N>> = simplifyRegex(re)
}

/** Applies some trivial simplifications to a [Regex]. Only applies simplification to top-level does not recurse. */
private fun <A> simplifyRegex(re: Regex<A>): Regex<A> = when (re) {
    is Empty -> re
    is Regex.Plus -> {
        val reFlattened = flattenPlusIfPossible(re)
        Regex.Plus(reFlattened.ops.filter { it !is Empty })
    }
    is Regex.Times -> {
        val reFlattened = flattenTimesIfPossible(re)
        when  {
            reFlattened.ops.any { it is Empty } -> Regex.getEmpty()
            else -> Regex.Times(reFlattened.ops.filter { it !is Regex.LetterOrEpsilon.Epsilon })
        }
    }
    is Regex.Star ->
        if (re.op is Empty || re.op is Regex.LetterOrEpsilon.Epsilon)
            Regex.getEpsilon()
        else
            re
    is Regex.LetterOrEpsilon.Epsilon -> re
    is Regex.LetterOrEpsilon.Letter -> re
}

/** Flatten nested [Regex.Times] (only one level, i.e., does not recurse). */
private fun <A> flattenTimesIfPossible(re: Regex.Times<A>): Regex.Times<A> {
    val ops = re.ops.flatMap { if (it is Regex.Times) it.ops else listOf(it) }
    return Regex.Times(ops) as Regex.Times<A>
}

/** Flatten nested [Regex.Plus] (only one level, i.e., does not recurse). */
private fun <A> flattenPlusIfPossible(re: Regex.Plus<A>): Regex.Plus<A> {
    val ops = re.ops.flatMap { if (it is Regex.Plus) it.ops else listOf(it) }
    return Regex.Plus(ops) as Regex.Plus<A>
}

/**
 * Performs [GraphToRegex] and then replaces the letters in the resulting regex (whose type is [Edge<N>]) by the
 *  corresponding labels from the given [LabelledGraphWithSourceAndSink].
 */
fun <N, E> labelledGraphToRegex(
    graph: LabelledGraphWithSourceAndSink<N, E>,
    edgesToLabels: (E) -> Regex<E> = { Regex.LetterOrEpsilon.Letter(it) },
    associativityRequirement: AssociativityRequirement
): Regex<E> {
    val regex = GraphToRegex(
        graph.labelledGraph,
        graph.source,
        graph.sink,
        associativityRequirement
    ).result

    return regex.transformLetters {
        val edgeLabel = graph.labelledGraph.getEdgeLabel(it.first, it.second)
        edgesToLabels(edgeLabel)
    }.transformPost { simplifyRegex(it) }
}

