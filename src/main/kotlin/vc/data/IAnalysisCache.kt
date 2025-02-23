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

package vc.data

import algorithms.SimpleDominanceAnalysis
import analysis.TACCommandGraph
import analysis.dataflow.*
import analysis.worklist.NaturalBlockScheduler
import com.certora.collect.*
import tac.NBId

interface IAnalysisCache {
    val graph: TACCommandGraph
    val def: IDefAnalysis
    val strictDef: StrictDefAnalysis
    val use: IUseAnalysis
    val lva: LiveVariableAnalysis
    val gvn : IGlobalValueNumbering
    val revertBlocks: Set<NBId>
    val domination: SimpleDominanceAnalysis<NBId>
    val variableLookup: Map<NBId, Set<TACSymbol.Var>>
    val naturalBlockScheduler: NaturalBlockScheduler
    val reachability: Map<NBId, TreapSet<NBId>>
}
