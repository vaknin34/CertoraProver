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

package analysis.controlflow

import analysis.smtblaster.Z3BlasterPool
import parallel.ParallelPool
import vc.data.CoreTACProgram
import verifier.BlockMerger

object InfeasiblePaths {
    fun doInfeasibleBranchAnalysisAndPruning(c: CoreTACProgram): CoreTACProgram {
        // Deep pruning of paths based on assumes and simple assignments
        // uses a pool of Z3 blaster pools and thus may incur a performance impact
        return ParallelPool.allocInScope({ Z3BlasterPool() }) {
            // we first identify a list of pruned branches
            InfeasiblePathAnalysis.findPrunedBranches(c, it).let {
                // then do the actual pruning, including removal of related blocks
                InfeasibleBranchPruning.pruneBranches(c, it).let {
                    // merge blocks to get a more tidy graph
                    BlockMerger.mergeBlocks(it)
                }
            }
        }
    }
}