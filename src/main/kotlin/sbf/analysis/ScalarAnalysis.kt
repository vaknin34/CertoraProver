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
import sbf.cfg.*
import sbf.disassembler.*
import sbf.domains.MemorySummaries
import sbf.domains.ScalarDomain
import sbf.fixpoint.WtoBasedFixpointOptions
import sbf.fixpoint.WtoBasedFixpointSolver

class ScalarAnalysis(val cfg: SbfCFG,
                     val globalsMap: GlobalVariableMap,
                     val memSummaries: MemorySummaries,
                     private val isEntryPoint:Boolean = true): IAnalysis<ScalarDomain> {

        private val preMap = mutableMapOf<Label, ScalarDomain>()
        private val postMap =  mutableMapOf<Label, ScalarDomain>()

        init {
            run()
        }

        override fun getPre(block:Label) = preMap[block]
        override fun getPost(block:Label) = postMap[block]
        override fun getCFG() = cfg
        override fun getMemorySummaries() = memSummaries
        override fun getGlobalVariableMap() = globalsMap

        private fun run() {
            val entry = cfg.getEntry()
            val bot = ScalarDomain.makeBottom()
            val top = ScalarDomain.makeTop()
            val solverOpts = WtoBasedFixpointOptions(2U,1U)
            val fixpo = WtoBasedFixpointSolver(bot, top, solverOpts, globalsMap, memSummaries)
            if (isEntryPoint) {
                preMap[entry.getLabel()] = ScalarDomain(initPreconditions = true)
            }
            fixpo.solve(cfg, preMap, postMap, null)
        }
}

typealias ScalarAnalysisRegisterTypes = AnalysisRegisterTypes<ScalarDomain>
