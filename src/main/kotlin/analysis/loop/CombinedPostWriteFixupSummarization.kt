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

package analysis.loop

import analysis.Loop
import analysis.TACCommandGraph
import analysis.smtblaster.IBlaster
import parallel.Parallel

class CombinedPostWriteFixupSummarization(graph: TACCommandGraph, blaster: IBlaster) {
    private val fixupZero = SimpleZeroWriteFixup(graph = graph, blaster = blaster)
    private val fixupConditional = ConditionalZeroWriteFixup(graph = graph, blaster = blaster)
    private val bitOpsFixup = BitOperationFixupSummarization(graph = graph, blaster = blaster)


    fun isPostWriteFixup(l: Loop, loopSummarization: LoopSummarization.LoopIterationSummary, w: ArrayLoopSummarization.WriteEvery, g: TACCommandGraph) : Parallel<CommonFixupReasoning.PostWriteFixup?> {
        val zJob = fixupZero.isPostWriteFixup(l, loopSummarization, w, g)
        val cJob = fixupConditional.isPostWriteFixup(l, loopSummarization, w, g)
        val eJob = bitOpsFixup.isPostWriteFixup(l, loopSummarization, w, g)
        return zJob.parallelBind(cJob, eJob) { s, d, e ->
            complete(setOf(s,d,e).filterNotNull().singleOrNull())
        }
    }
}