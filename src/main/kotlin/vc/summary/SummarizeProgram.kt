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

package vc.summary

import algorithms.Regex
import algorithms.RegexOps
import algorithms.labelledGraphToRegex
import analysis.CmdPointer
import analysis.LTACCmd
import analysis.TACCommandGraph
import datastructures.*
import vc.data.TACCmd

object SummarizeProgram {


    fun <SUMMARY : HasTACSummaryTransformula> summarizeTAC(
        prog: TACCommandGraph,
        summaryComputation: ComputeTACSummary<SUMMARY>
    ): SUMMARY {
        val graph: LabelledGraphWithSourceAndSink<NodeId, SUMMARY> =
            convertTACCommandGraphToLabelledGraph(
                prog,
                summaryComputation::summarizeCmd
            )

        val replacedEdgesWithSummaries = labelledGraphToRegex(
            graph,
            ::edgeLabelToRegexOptimizeAbsorbAndNop,
            summaryComputation.associativityRequirement
        )

        return summarizeRegexTAC(summaryComputation, replacedEdgesWithSummaries)
    }

    private fun <SUMMARY : HasTACSummaryTransformula> summarizeRegexTAC(
        summaryComputation: ComputeTACSummary<SUMMARY>,
        replacedEdgesWithSummaries: Regex<SUMMARY>
    ): SUMMARY = RegexOps(
        plus = summaryComputation::parallelComposition,
        times = summaryComputation::sequentialComposition,
        star = summaryComputation::summarizeLoop,
        associativityRequirement = summaryComputation.associativityRequirement
    ).reduceRegex(replacedEdgesWithSummaries)

    /**
     *
     * away branches that contain an [ComputeTACSummaryProjectAndPrune.AbsorberUnreachSummary], and  throwing away
     * statements that have a [ComputeTACSummaryTransFormula.TACSummaryTransFormula.NopSummary].
     */
    private fun <L> edgeLabelToRegexOptimizeAbsorbAndNop(l: L): Regex<L> {
        val tstf = l as HasTACSummaryTransformula
        return when {
            tstf.getTACSummaryTransformula().isUnreachable ->
                Regex.getEmpty()
            tstf.getTACSummaryTransformula().isNop ->
                Regex.getEpsilon()
            else -> Regex.LetterOrEpsilon.Letter(l)
        }
    }


    /**
     * Notes:
     *  - converts a graph with labels on the nodes to a graph with labels on the edges, basic ideas:
     *     - nodes in the processed graph are identified by [CmdPointer]s (might wrap this once more in the future ...)
     *     - edges in the processed graph are labelled by the summary of an [LTACCmd]
     *     - if there is exactly one successor, the summarized [LTACCmd] belonging to the node's [CmdPointer] labels the
     *       outgoing edge
     *     - if there is no successor, we introduce a fresh sink node (that does not correspond to a [CmdPointer]
     *     - before a fork (i.e. if there are two successors), we introduce a fresh fork node (that does not correspond to a
     *       [CmdPointer]
     *
     */
    private fun <L> convertTACCommandGraphToLabelledGraph(
        prog: TACCommandGraph,
        summarizeCmd: (LTACCmd) -> L
    ): LabelledGraphWithSourceAndSink<NodeId, L> {

        val edgeRelation: MutableMultiMap<NodeId, NodeId> =
            mutableMultiMapOf<NodeId, NodeId>()
        val labelMapping: MutableMap<Pair<NodeId, NodeId>, L> =
            mutableMapOf()

        val sourceNodes: MutableSet<NodeId.CmdPtrNode> = mutableSetOf()
        val sinkNodes: MutableSet<NodeId.SinkNode> = mutableSetOf()
        val returningSinkNodes: MutableSet<NodeId.SinkNode> = mutableSetOf()

        prog.commands.forEach { cmd ->

            val sumRegex = summarizeCmd(cmd)

            if (prog.pred(cmd.ptr).isEmpty()) {
                // node is a (the) start node
                sourceNodes.add(NodeId.CmdPtrNode(cmd.ptr))
            }

            val successors = prog.succ(cmd.ptr)
            when (successors.size) {
                0 -> { // node is a sink
                    val cmdPtrId = NodeId.CmdPtrNode(cmd.ptr)
                    val succPtrId = NodeId.SinkNode(cmd.ptr)
                    sinkNodes.add(succPtrId)
                    if (cmd.cmd is TACCmd.Simple.ReturnCmd || cmd.cmd is TACCmd.Simple.ReturnSymCmd) { // TODO: not a good criterion
                        returningSinkNodes.add(succPtrId)
                    }
                    edgeRelation.add(cmdPtrId, succPtrId)
                    labelMapping[cmdPtrId to succPtrId] = sumRegex
                }

                1 -> {
                    val succPtr = successors.first()
                    val cmdPtrId = NodeId.CmdPtrNode(cmd.ptr)
                    val succPtrId = NodeId.CmdPtrNode(succPtr)
                    edgeRelation.add(cmdPtrId, succPtrId)
                    labelMapping[cmdPtrId to succPtrId] = sumRegex
                }

                2 -> {
                    // control flow forks after this node
                    val succList = successors.toList()
                    val succPtr1 = succList[0]
                    val succPtr2 = succList[1]

                    val cmdPtrId = NodeId.CmdPtrNode(cmd.ptr)
                    val forkNodeId = NodeId.ForkNode(cmd.ptr, succPtr1, succPtr2)
                    val succPtrId1 = NodeId.CmdPtrNode(succPtr1)
                    val succPtrId2 = NodeId.CmdPtrNode(succPtr2)

                    edgeRelation.add(cmdPtrId, forkNodeId)
                    edgeRelation.add(forkNodeId, succPtrId1)
                    edgeRelation.add(forkNodeId, succPtrId2)
                    labelMapping[cmdPtrId to forkNodeId] = sumRegex

                    val srcBlockId = cmd.ptr.block
                    val tgtBlockId1 = succPtr1.block
                    val tgtBlockId2 = succPtr2.block
                    check(srcBlockId != tgtBlockId1 && srcBlockId != tgtBlockId2 && tgtBlockId1 != tgtBlockId2)
                    { "that there is a branching between the commands means that they come from different blocks, right?" }

                    val pathCondition1 = prog.pathConditionsOf(srcBlockId)[tgtBlockId1]!!
                    val pathCondition2 = prog.pathConditionsOf(srcBlockId)[tgtBlockId2]!!

                    labelMapping[forkNodeId to succPtrId1] = summarizeCmd(
                        LTACCmd(
                            CmdPointer(tgtBlockId1, -1), // TODO: is index -1 a good solution here??
                            pathCondition1.getAsAssumeCmd()
                        )
                    )
                    labelMapping[forkNodeId to succPtrId2] = summarizeCmd(
                        LTACCmd(
                            CmdPointer(tgtBlockId2, -1), // TODO: is index -1 a good solution here??
                            pathCondition2.getAsAssumeCmd()
                        )
                    )
                }

                else -> throw UnsupportedOperationException("TODO convertTACCommandGraphToLabelledGraph for $successors of $cmd")
            }
        }

        check(sourceNodes.size == 1)
        { "summarizing methods with more than one entry point is currently not supported" }
        val startNode = sourceNodes.first()

        check(sinkNodes.size == 1 || returningSinkNodes.size == 1)
        { "expecting one return node" }
        val endNode = if (sinkNodes.size == 1) sinkNodes.first() else returningSinkNodes.first()

        return LabelledGraphWithSourceAndSink(
            LabelledGraph(
                edgeRelation,
                labelMapping
            ), startNode, endNode
        )
    }


    private sealed class NodeId {
        data class CmdPtrNode(val cmdPtr: CmdPointer) : NodeId() {
            override fun toString(): String {
                return "${cmdPtr.block}L${cmdPtr.pos}"
            }
        }

        data class SinkNode(val preceedingCmdPtr: CmdPointer) : NodeId()
        data class ForkNode(val preceedingCmdPtr: CmdPointer, val ifBranch: CmdPointer, val thenBranch: CmdPointer) :
            NodeId()
    }
}

