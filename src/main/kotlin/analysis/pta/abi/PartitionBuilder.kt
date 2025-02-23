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

package analysis.pta.abi

import algorithms.UnionFind
import analysis.CmdPointer
import analysis.pta.*
import analysis.pta.TypedSetVisitor.Companion.accept
import com.certora.collect.*
import datastructures.stdcollections.*
import utils.AmbiSerializable
import utils.KSerializable
import utils.tryAs
import utils.unused
import vc.data.UniqueIdEntity
import java.math.BigInteger

@KSerializable
@Treapable
data class UnindexedPartitionInfo(
    val info: Map<UnindexedPartition, Map<PartitionField, UnindexedPartition>>
): AmbiSerializable, UniqueIdEntity<UnindexedPartitionInfo> {
   override fun mapId(f: (Any, Int, () -> Int) -> Int) = copy(
        info = info.map { (k, v) ->
            k.mapId(f) to v.mapValues { (_, v) -> v.mapId(f) }
        }.toMap()
    )
}


class PartitionBuilder(private val pta: IPointsToInformation) {
    private val equivClass = UnionFind<PTANode>()
    private val partitions = mutableMapOf<PTANode, UnindexedPartition>()
    private val contextSentitivePartitions = mutableMapOf<Pair<PTANode, *>, UnindexedPartition>()
    private val fieldReps =
        treapMapBuilderOf<UnindexedPartition, TreapMap<PartitionField, PTANode>>()

    private fun Iterable<IPointsToSet>.getRepresentative(): PTANode =
        equivClass.getRepresentative(this.asSequence().flatMap { it.nodes }.first())

    /**
     * Records the object pta nodes (the domain) for which all child struct fields must be unified.
     * The codomain are the field nodes encountered during [mergeFields] calls, which are eagerly
     * unified with the other nodes already present.
     *
     * In other words, the existence of a PTA node in this map as a key indicates that all struct fields nodes
     * with that node as a parent must be unified with all other struct field nodes that share the same parent.
     */
    private val mergeParents = mutableMapOf<PTANode, TreapSet<PTANode>>()

    fun mergeFields(fields: Iterable<IPointsToSet>) =
        mergeFieldNodes(fields.flatMap { it.nodes })
    fun mergeFields(fields: IPointsToSet) =
        mergeFieldNodes(fields.nodes)

    private fun mergeFieldNodes(nodes: Collection<PTANode>) {
        if (nodes.isNotEmpty()) {
            nodes.forEach { node ->
                equivClass.register(node)
                if(node is StructFieldNode && node.parentNode in mergeParents) {
                    val curr = mergeParents.getOrDefault(node.parentNode, treapSetOf())
                    if(!curr.isEmpty()) {
                        equivClass.union(curr.first(), node)
                    }
                    mergeParents[node.parentNode] = curr + node
                }
            }
            equivClass.union(nodes)
        }
    }

    @Synchronized
    fun getPartition(where: CmdPointer, fields: Iterable<IPointsToSet>): UnindexedPartition {
        unused(where)
        return getPartition(fields.asSequence().flatMap { it.nodes }.first())
    }

    @Synchronized
    fun <T> getPartition(where: CmdPointer, context: T, fields: Iterable<IPointsToSet>) : UnindexedPartition {
        return getPartition(fields.getRepresentative(), context).also { p ->
            fields.forEach {
                ingestContents(p, where, it)
            }
        }
    }

    @Synchronized
    fun <T> getPartition(node: PTANode, context: T) : UnindexedPartition {
        check(isSingleton(node)) {
            "Context-sensitive partitions are only usable for singleton nodes"
        }
        return contextSentitivePartitions.getOrPut(node to context) { UnindexedPartition.new() }
    }

    private fun getPartition(node: PTANode): UnindexedPartition {
        val rep = equivClass.getRepresentative(node)
        return partitions.getOrPut(rep) { UnindexedPartition.new() }
    }

    @Synchronized
    fun getPartition(nodes: Collection<PTANode>): UnindexedPartition {
        val first = nodes.first()
        check(nodes.all { equivClass.areEqual(it, first) }) { "Nodes $nodes are not in the same partition" }
        return getPartition(first)
    }

    @Synchronized
    fun getPartitionInfo(): UnindexedPartitionInfo = UnindexedPartitionInfo(
        fieldReps.build().mapValues { (_, v) ->
            v.mapValues { (_, n) ->
                getPartition(n)
            }
        }
    )


    // intern table for fields, to reduce memory usage
    private val fields = mutableMapOf<PartitionField, PartitionField>()
    private fun intern(field: PartitionField): PartitionField = fields.computeIfAbsent(field) { it }

    private fun ingestContents(fieldPart: UnindexedPartition, where: CmdPointer, set: IPointsToSet) {

        val contents = (set as? WritablePointsToSet)?.let { pta.contentsOf(where, it) }

        var fields = fieldReps[fieldPart].orEmpty()

        fun addField(field: PartitionField, s: IPointsToSet) {
            val existingRep = fields[field]
            if (existingRep != null) {
                mergeFieldNodes(s.nodes + existingRep)
            } else {
                mergeFieldNodes(s.nodes)
                fields += intern(field) to s.nodes.first()
            }
        }

        val result = contents?.tryAs<TypedPointsToSet>()?.accept(
            where,
            pta,
            object : TypedSetVisitor {
                override fun arrayField(s: IndexedWritableSet): VisitResult {
                    addField(PartitionField.ArrayElement(s.elementSize), s)
                    return TypedSetVisitor.OK
                }
                override fun arrayLengthField(s: IPointsToSet): VisitResult {
                    addField(PartitionField.ArrayLength, s)
                    return TypedSetVisitor.OK
                }
                override fun structField(o: BigInteger, s: WritablePointsToSet): VisitResult {
                    addField(PartitionField.StructField(o), s)
                    return TypedSetVisitor.OK
                }
                override fun primitive() {
                    // ignored
                }
            }
        )
        check(result == TypedSetVisitor.OK) { "Failed to ingest contents of $set at $where: $result" }

        if (fields.isNotEmpty()) {
            fieldReps[fieldPart] = fields
        }
    }

    @Synchronized
    fun isSingleton(sets: Iterable<IPointsToSet>) : Boolean {
        return sets.toList().singleOrNull()?.let { ptaSet ->
            ptaSet.nodes.singleOrNull()?.let { node ->
                isSingleton(node)
            }
        } == true
    }

    @Synchronized
    fun isSingleton(it: PTANode): Boolean {
        return equivClass.isRegistered(it) && equivClass.getEquivalenceClass(it) == setOf(it)
    }

    @Synchronized
    fun registerMergeParents(mergedParents: Set<PTANode>) {
        mergedParents.forEach {
            mergeParents[it] = treapSetOf()
        }
    }
}
