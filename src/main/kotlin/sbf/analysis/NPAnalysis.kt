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

import analysis.Direction
import analysis.JoinLattice
import sbf.cfg.*
import sbf.disassembler.Label
import sbf.domains.MemorySummaries
import sbf.domains.NPDomain
import sbf.domains.VariableFactory
import datastructures.stdcollections.*
import sbf.disassembler.GlobalVariableMap


data class NPDomainState(val state: NPDomain) {
    companion object {
        val bottom = NPDomainState(NPDomain.mkBottom())

        val lattice = object : JoinLattice<NPDomainState> {
            override fun join(x: NPDomainState, y: NPDomainState): NPDomainState {
                return NPDomainState(x.state.join(y.state))
            }

            override fun equiv(x: NPDomainState, y: NPDomainState): Boolean =
                x.state.lessOrEqual(y.state) && y.state.lessOrEqual(x.state)
        }
    }
}


class NPAnalysis(val cfg: MutableSbfCFG,
                 globalsMap: GlobalVariableMap,
                 memSummaries: MemorySummaries) :
    SbfBlockDataflowAnalysis<NPDomainState>(
        cfg,
        NPDomainState.lattice,
        NPDomainState.bottom,
        Direction.BACKWARD
    ) {

    /** Used by the NPDomain to represent contents of stack slots **/
    private val vFac = VariableFactory()
    /**
     * We need to run a forward analysis to know whether a pointer points to the
     * stack or not. Note that we run only a scalar domain so the analysis will be
     * quite cheap but imprecise.
     **/
    private val fwdAnalysis = ScalarAnalysis(cfg, globalsMap, memSummaries)
    val registerTypes = ScalarAnalysisRegisterTypes(fwdAnalysis)
    /** Exit blocks of the cfg **/
    val exits: MutableSet<Label> = datastructures.stdcollections.mutableSetOf()

    init {
        // Annotate the cfg with extra info that might help analysis precision
        propagateAssumptions(cfg, registerTypes) /* this requires cfg to be mutable */

        // Collect exits of the cfg
        for (b in cfg.getBlocks().values) {
            if (b.getInstructions().any {inst -> inst.isAssertOrSatisfy()}) {
                exits.add(b.getLabel())
            }
        }

        // run the backward analysis
        runAnalysis()
    }

    fun getPreconditionsAtEntry(label: Label): NPDomain? {
        return blockOut[label]?.state
    }

    fun contains(np: NPDomain, cond: Condition): Boolean {
        return np.contains(NPDomain.getLinCons(cond, vFac))
    }

    fun isBottom(np: NPDomain, locInst: LocatedSbfInstruction, cond: Condition): Boolean {
        return np.analyzeAssume(cond, locInst, vFac, registerTypes).isBottom()
    }

    fun populatePreconditionsAtInstruction(label:Label): Map<LocatedSbfInstruction, NPDomain>{
        val block = cfg.getBlock(label)
        return if (block != null) {
            var outVal = if (block.getInstructions().any{ it is SbfInstruction.Exit}) {
                NPDomain.mkTrue()
            } else {
                NPDomain.mkBottom()
            }
            for (succ in block.getSuccs()) {
                val succVal = getPreconditionsAtEntry(succ.getLabel())
                if (succVal != null) {
                    outVal = outVal.join(succVal)
                }
            }
            outVal.analyze(block, vFac, registerTypes, propagateOnlyFromAsserts = true, computeInstMap = true).second
        } else {
            mutableMapOf()
        }
    }

    override fun transform(inState: NPDomainState, block: SbfBasicBlock): NPDomainState {
        val inNPVal = if (exits.contains(block.getLabel())) {
            NPDomain.mkTrue()
        } else {
            inState.state
        }
       return NPDomainState(inNPVal.analyze(block, vFac, registerTypes))
    }
}
