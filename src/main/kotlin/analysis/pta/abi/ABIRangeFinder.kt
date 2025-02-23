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

import datastructures.stdcollections.*
import analysis.CmdPointer
import analysis.maybeAnnotation
import analysis.maybeNarrow
import analysis.pta.ABICodeFinder
import utils.*
import vc.data.CoreTACProgram
import vc.data.TACCmd
import vc.data.canReach
import java.util.stream.Collectors

abstract class ABIRangeFinder<T: ABICodeFinder.Source> {
    fun findRangeFor(core: CoreTACProgram, id: Int) : List<Pair<CmdPointer, CmdPointer>>? {
        val starts = core.parallelLtacStream().filter {
            it.maybeNarrow<TACCmd.Simple.AnnotationCmd>()?.cmd?.check(ABIAnnotator.REGION_START) {
                it.sources.singleOrNull()?.let(this::downcast)?.id == id
            } == true
        }.collect(Collectors.toList())
        val rangeId = starts.mapTo(mutableSetOf()) {
            it.maybeAnnotation(ABIAnnotator.REGION_START)!!.id
        }
        val endPoints = core.parallelLtacStream().filter {
            it.maybeNarrow<TACCmd.Simple.AnnotationCmd>()?.cmd?.check(ABIAnnotator.REGION_END) {
                it.id in rangeId
            } == true
        }.collect(Collectors.toList())
        if(endPoints.size != starts.size) {
            return null
        }

        return starts.monadicMap { start ->
            val regionId = start.maybeAnnotation(ABIAnnotator.REGION_START)?.id ?: return@monadicMap null
            val end = endPoints.singleOrNull { it.maybeAnnotation(ABIAnnotator.REGION_END)?.id == regionId }
                ?: return@monadicMap null
            start.ptr to end.ptr
        }
    }

    /**
     * @returns the unique range r in [ranges] (if it exists) such that:
     *          for all q in [ranges]\{r}, q can reach r.
     *
     *
     * The idea here is that the requirement there be a single such range prevents something cursed like:
     *
     *   range1
     *   range2
     *   while(*) {
     *      if(*) {
     *         range3
     *      } else {
     *         range4
     *      }
     *   }
     *
     */
    fun finalRange(core: CoreTACProgram, ranges: List<Pair<CmdPointer, CmdPointer>>): Pair<CmdPointer, CmdPointer>? {
        return ranges.singleOrNull() { (candStart, _) ->
            ranges.all { (predStart, _) ->
                predStart == candStart
                    || core.analysisCache.reachability.canReach(predStart, candStart)
            }
        }
    }

    abstract fun downcast(x: ABICodeFinder.Source) : T?
}


