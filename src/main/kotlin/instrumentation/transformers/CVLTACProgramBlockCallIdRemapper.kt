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

package instrumentation.transformers

import allocator.Allocator
import com.certora.collect.*
import datastructures.stdcollections.*
import tac.CallId
import tac.MetaMap
import tac.NBId.Companion.ROOT_CALL_ID
import utils.*
import vc.data.*

object CVLTACProgramBlockCallIdRemapper {
    /**
     * @return [prog] with all blocks with 0-valued (default valued) callee indices updated to match the call index
     * of [newCallId].
     * Note that we don't update the callee idx of blocks with non-default calleeIdx because those apparently already
     * belong to some separate entity (e.g. a call to another function) so we don't want to lose that information.
     *
     * @why For UI/CFG display purposes, this allows to e.g. have all blocks of a CVL function have the same calleeIdx
     *      so it will show as a separate subgraph in the .html dump.
     */
    fun remapIds(prog: CVLTACProgram, newCallId: CallId, forceRemap: Boolean = false): CVLTACProgram {
        val newNBIds = prog.blockgraph.keys.associateWith { oldId ->
            val newCalleeIdx = if (forceRemap) {
                newCallId
            } else {
                oldId.calleeIdx.takeIf { it != ROOT_CALL_ID } ?: newCallId
            }
            oldId.copy(
                calleeIdx = newCalleeIdx, freshCopy = Allocator.getFreshId(
                    Allocator.Id.BLOCK_FRESH_COPY
                )
            )
        }.toMap()

        val mapper = object : DefaultTACCmdMapper() {
            override fun mapJumpCmd(t: TACCmd.Simple.JumpCmd): TACCmd.Simple {
                return super.mapJumpCmd(t.withDst(newNBIds[t.dst]!!))
            }

            override fun mapJumpICmd(t: TACCmd.Simple.JumpiCmd): TACCmd.Simple {
                return super.mapJumpICmd(t.copy(dst = newNBIds[t.dst]!!, elseDst = newNBIds[t.elseDst]!!))
            }

            override fun mapSummaryCmd(t: TACSummary, meta: MetaMap): TACCmd.Simple {
                val newT = when (t) {
                    is ConditionalBlockSummary -> t.remapBlocks { newNBIds[it] }

                    else -> t
                }

                return super.mapSummaryCmd(newT, meta)
            }
        }

        return prog.copy(
            blockgraph = prog.blockgraph.entries.associateTo(MutableBlockGraph()) { (key, dsts) ->
                newNBIds[key]!! to dsts.updateElements { dst -> newNBIds[dst]!! }
            },
            code = prog.code.entries.associate { (key, block) ->
                newNBIds[key]!! to block.map { cmd -> (cmd as? TACCmd.Simple)?.let(mapper::map) ?: cmd }
            }
        )



    }
}
