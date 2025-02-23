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

package sbf.cfg

import sbf.analysis.NPAnalysis
import datastructures.stdcollections.*

/**
 *  Replace
 *     dst := select(cond, trueVal, falseVal)
 *  with
 *     dst := trueVal
 *     assume(cond)   if we can infer that dst == trueVal is a necessary precondition to reach all the assert's
 *  or
 *     dst := falseVal
 *     assume(!cond)  if we can infer that dst == falseVal otherwise
 */
fun lowerSelectToAssume(cfg: MutableSbfCFG, npAnalysis: NPAnalysis) {
    for (block in cfg.getMutableBlocks().values) {
        val selects = ArrayList<LocatedSbfInstruction>()
        for (locInst in block.getLocatedInstructions()) {
            if (locInst.inst is SbfInstruction.Select) {
                selects.add(locInst)
            }
        }
        if (selects.isEmpty()) {
            continue
        }

        val npAtInst = npAnalysis.populatePreconditionsAtInstruction(block.getLabel())
        // In this loop we cannot modify the block because we are accessing to npAnalysis
        val replaceMap = mutableMapOf<LocatedSbfInstruction, Pair<SbfInstruction, SbfInstruction>>()
        for (locSelectInst in selects) {
            val select = locSelectInst.inst
            check(select is SbfInstruction.Select)
            val np = npAtInst[locSelectInst] ?: continue
            if (!np.isBottom()) {
                val trueCst = Condition(CondOp.EQ, select.dst, select.trueVal)
                val falseCst = Condition(CondOp.EQ, select.dst, select.falseVal)
                val newMetadata = select.metaData.plus(Pair(SbfMeta.LOWERED_SELECT, ""))
                val (newAssumeInst, newSelectDstVal) = if (npAnalysis.contains(np, trueCst) && npAnalysis.isBottom(np, locSelectInst, falseCst)) {
                        Pair(SbfInstruction.Assume(select.cond, newMetadata), select.trueVal)
                    } else if (npAnalysis.contains(np, falseCst) && npAnalysis.isBottom(np, locSelectInst, trueCst)) {
                        Pair(SbfInstruction.Assume(select.cond.negate(), newMetadata), select.falseVal)
                    } else {
                        Pair(null, null)
                    }
                if (newAssumeInst != null && newSelectDstVal != null) {
                    val newAssignInst = SbfInstruction.Bin(BinOp.MOV, select.dst, newSelectDstVal, true, null, null, null, newMetadata)
                    replaceMap[locSelectInst] = Pair(newAssignInst, newAssumeInst)
                }
            }
        }

        var numAdded = 0 // Used to adjust indices after a havoc instruction is inserted
        for ((locSelectInst, pairOfInsts) in replaceMap) {
            val newAssignInst = pairOfInsts.first
            val newAssumeInst = pairOfInsts.second
            block.add(locSelectInst.pos + numAdded, newAssignInst)
            block.replaceInstruction(locSelectInst.pos + numAdded + 1, newAssumeInst)
            numAdded++
        }
    }
}
