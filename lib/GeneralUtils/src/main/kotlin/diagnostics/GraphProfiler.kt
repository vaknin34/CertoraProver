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

package diagnostics

import datastructures.stdcollections.*
import kotlin.io.*
import kotlin.io.path.*
import kotlinx.coroutines.yield
import kotlinx.serialization.json.JsonPrimitive
import parallel.coroutines.onThisThread
import utils.*
import java.io.BufferedWriter
import java.nio.file.*

/**
    Generates dumps of graphs, for consumption in a profiler.  We use the Chromium heap dump format, which can be viewed
    in the profiler that comes with Chrome, Edge, VS Code, or Node, and can be analyzed by other tools as well.
 */
object GraphProfiler {
    /** A node in the graph.  Node types are analogous to JavaScript types. */
    sealed class Node {
        /** The value that this node represents. Used for equality comparisons! */
        abstract val value: Any

        /** The size that this node contributes to the profile.  Can be zero. */
        abstract val selfSize: Int

        /** Edges to successor nodes */
        abstract val edges: Sequence<Edge>

        internal abstract val nodeType: NodeType
        internal abstract val nodeName: Any

        data class Object(
            override val value: Any,
            val className: Any,
            override val selfSize: Int,
            override val edges: Sequence<Edge>
        ) : Node() {
            internal override val nodeType get() = NodeType.OBJECT
            internal override val nodeName get() = className
        }

        data class Array(
            override val value: Any,
            val className: Any,
            override val selfSize: Int,
            override val edges: Sequence<Edge>
        ) : Node() {
            internal override val nodeType get() = NodeType.ARRAY
            internal override val nodeName get() = className
        }

        data class String(
            override val value: Any,
            override val selfSize: Int
        ) : Node() {
            override val edges get() = sequenceOf<Edge>()
            internal override val nodeType get() = NodeType.STRING
            internal override val nodeName get() = value
        }

        data class Number(
            override val value: kotlin.Number,
            override val selfSize: Int
        ) : Node() {
            override val edges get() = sequenceOf<Edge>()
            internal override val nodeType get() = NodeType.NUMBER
            internal override val nodeName get() = value
        }

        /** Synthetic root object */
        internal data class Root(
            val syntheticType: SyntheticType,
            override val edges: Sequence<Edge>
        ) : Node() {
            override val value get() = this
            override val selfSize get() = 0

            internal override val nodeType get() = NodeType.SYNTHETIC
            internal override val nodeName get() = syntheticType.typeName
        }
    }


    sealed class Edge {
        abstract val to: Node
        internal abstract val edgeType: EdgeType

        data class Property(val name: String, override val to: Node) : Edge() {
            internal override val edgeType get() = EdgeType.PROPERTY
        }

        data class Element(val index: Int, override val to: Node) : Edge() {
            internal override val edgeType get() = EdgeType.ELEMENT
        }
    }

    fun writeProfile(path: Path, roots: Sequence<Node>) = path.bufferedWriter().use { writeProfile(it, roots) }

    fun writeProfile(out: BufferedWriter, roots: Sequence<Node>) {
        // See the Chromium heap dump format, helpfully documented by Microsoft here:
        // https://learn.microsoft.com/en-us/microsoft-edge/devtools-guide-chromium/memory-problems/heap-snapshot-schema

        // Note that we jump through some hoops here to avoid ever storing the whole graph, since these might be quite
        // large.

        // Generate the self-describing snapshot metadata.
        val nodeTypes = NodeType.values().map { it.typeName }.joinToString { "\"$it\"" }
        val nodeFields = NodeField.values().map { it.fieldName }.joinToString { "\"$it\"" }
        val nodeFieldTypes = NodeField.values().mapNotNull { it.type?.typeName }.joinToString { "\"$it\"" }
        val edgeFields = EdgeField.values().map { it.fieldName }.joinToString { "\"$it\"" }
        val edgeFieldTypes = EdgeField.values().mapNotNull { it.typeName }.joinToString { "\"$it\"" }
        val edgeTypes = EdgeType.values().map { it.typeName }.joinToString { "\"$it\"" }
        out.write("""{"snapshot":{"meta":{"node_fields":[$nodeFields],"node_types":[[$nodeTypes],$nodeFieldTypes],"edge_fields":[$edgeFields],"edge_types":[[$edgeTypes],$edgeFieldTypes]}""")

        var nodeCount = 0L
        var edgeCount = 0L
        val nodeIds = mutableMapOf<Any, Long>()

        // Tell the profiler that all of our objects are rooted.
        val gcRoots = Node.Root(
            SyntheticType.GC_ROOTS,
            roots.mapIndexed { i, it -> Edge.Element(i, it) }
        )

        // Count nodes and edges, and assign IDs to nodes. We use a suspend function to avoid stack overflow due to
        // recursion.
        suspend fun count(node: Node) {
            yield() // Avoid stack overflow
            if (node.value !in nodeIds) {
                nodeIds[node.value] = nodeCount++
                node.edges.forEach { edge ->
                    edgeCount++
                    count(edge.to)
                }
            }
        }
        onThisThread { count(gcRoots) }
        out.write(""","node_count":$nodeCount,"edge_count":$edgeCount,"trace_function_count":0""")

        // Track strings so we can write the string table later.
        val strings = mutableMapOf<Any, Int>()
        fun stringOrdinal(s: Any) = strings.getOrPut(s) { strings.size }

        // Write the "nodes" table
        out.write("\n},\"nodes\":[")
        val written = mutableSetOf<Any>()
        suspend fun writeNode(node: Node, first: Boolean) {
            if (written.add(node.value)) {
                yield() // Avoid stack overflow
                val typeOrdinal = node.nodeType.ordinal
                val nameOrdinal = stringOrdinal(node.nodeName)

                val id = nodeIds[node.value] ?: error("Inconsistent node values for node $node")
                val selfSize = node.selfSize
                val edges = node.edges.toList()
                val nodeEdgeCount = edges.size

                out.write("\n")
                if (!first) { out.write(",") }
                out.write("$typeOrdinal,$nameOrdinal,$id,$selfSize,$nodeEdgeCount,0,0")

                edges.forEach {
                    writeNode(it.to, false)
                }
            }
        }
        onThisThread { writeNode(gcRoots, true) }

        // Write the "edges" table
        out.write("\n],\"edges\":[")
        written.clear()
        suspend fun writeEdges(node: Node, firstNode: Boolean) {
            if (written.add(node.value)) {
                yield()
                val edges = node.edges.toList()
                var firstEdge = true
                edges.forEach { edge ->
                    val typeOrdinal = edge.edgeType.ordinal
                    val edgeNameOrIndex = when (edge) {
                        is Edge.Property -> stringOrdinal(edge.name)
                        is Edge.Element -> edge.index
                    }
                    val toNodeId = nodeIds[edge.to.value] ?: error("Inconsistent node values for node $node")
                    val toNodeIndex = toNodeId * NodeField.values().size

                    out.write("\n")
                    if (!firstNode || !firstEdge) { out.write(",") }
                    out.write("$typeOrdinal,$edgeNameOrIndex,$toNodeIndex")

                    firstEdge = false
                }
                edges.forEach {
                    writeEdges(it.to, false)
                }
            }
        }
        onThisThread { writeEdges(gcRoots, true) }

        // Write the "strings" table
        out.write("\n],\"strings\":[")
        strings.map { (string, ordinal) -> string to ordinal }.sortedBy { it.second }.forEachIndexed { i, (string, _) ->
            val encoded = JsonPrimitive(string.toString()).toString()
            out.write("\n")
            if (i != 0) { out.write(",") }
            out.write("$encoded")
        }

        // And we're done.
        out.write("\n]}")
    }

    //
    // Constant values from the Chromium heap dump format.  We probably don't need all of these, but we're more likely
    // to be compatible with more tools if we output everything.
    //
    internal enum class NodeType(val typeName: String) {
        HIDDEN("hidden"),
        ARRAY("array"),
        STRING("string"),
        OBJECT("object"),
        CODE("code"),
        CLOSURE("closure"),
        REGEXP("regexp"),
        NUMBER("number"),
        NATIVE("native"),
        SYNTHETIC("synthetic"),
        CONCATENATED_STRING("concatenated string"),
        SLICED_STRING("sliced string"),
        SYMBOL("symbol"),
        BIGINT("bigint"),
        OBJECT_SHAPE("object shape")
    }

    internal enum class NodeField(val fieldName: String, val type: NodeType?) {
        TYPE("type", null),
        NAME("name", NodeType.STRING),
        ID("id", NodeType.NUMBER),
        SELF_SIZE("self_size", NodeType.NUMBER),
        EDGE_COUNT("edge_count", NodeType.NUMBER),
        TRACE_NODE_ID("trace_node_id", NodeType.NUMBER),
        DETACHEDNESS("detachedness", NodeType.NUMBER)
    }

    internal enum class EdgeField(val fieldName: String, val typeName: String?) {
        TYPE("type", null),
        NAME_OR_INDEX("name_or_index", "string_or_number"),
        TO_NODE("to_node", "node")
    }

    internal enum class EdgeType(val typeName: String) {
        CONTEXT("context"),
        ELEMENT("element"),
        PROPERTY("property"),
        INTERNAL("internal"),
        HIDDEN("hidden"),
        SHORTCUT("shortcut"),
        WEAK("weak")
    }

    internal enum class SyntheticType(val typeName: String) {
        GC_ROOTS("GC roots")
    }
}
