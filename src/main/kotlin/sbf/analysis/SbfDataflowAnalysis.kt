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

package sbf.analysis

import datastructures.stdcollections.*
import analysis.*
import sbf.cfg.*
import sbf.disassembler.Label
import utils.mapToSet

private object SbfGraphView: GraphBlockView<SbfCFG, SbfBasicBlock, Label> {
    override fun elab(g: SbfCFG, l: Label): SbfBasicBlock = g.getBlock(l)!!

    override fun succ(g: SbfCFG, src: SbfBasicBlock) = src.getSuccs()

    override fun pred(g: SbfCFG, src: SbfBasicBlock) = src.getPreds()

    override fun blockGraph(g: SbfCFG): Map<Label, Set<Label>> =
        g.getBlocks().mapValues { (_, bb: SbfBasicBlock) ->
            bb.getSuccs().mapToSet { it.getLabel() }
        }

    override fun blockId(b: SbfBasicBlock): Label = b.getLabel()

}

private object SbfCommandView: BlockCommandView<SbfBasicBlock, LocatedSbfInstruction, LocatedSbfInstruction> {
    override fun commands(b: SbfBasicBlock): List<LocatedSbfInstruction> = b.getLocatedInstructions()

    override fun ptr(c: LocatedSbfInstruction): LocatedSbfInstruction = c
}

abstract class SbfCommandDataflowAnalysis<T: Any>(
    graph: SbfCFG,
    lattice: JoinLattice<T>,
    bottom: T,
    direction: Direction,
    ): CommandDataflowAnalysis<SbfCFG, SbfBasicBlock, Label, LocatedSbfInstruction, LocatedSbfInstruction, T>(
           graph,
           lattice,
           bottom,
           direction,
           SbfGraphView,
           SbfCommandView,
       )


abstract class SbfBlockDataflowAnalysis<T: Any>(
    graph: SbfCFG,
    lattice: JoinLattice<T>,
    bottom: T,
    direction: Direction,
): BlockDataflowAnalysis<SbfCFG, SbfBasicBlock, Label, T>(
    graph,
    lattice,
    bottom,
    direction,
    SbfGraphView
)
