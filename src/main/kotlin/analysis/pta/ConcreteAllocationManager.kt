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

@file:Suppress("ImportStdCollections")
package analysis.pta

import analysis.CmdPointer
import analysis.LTACCmd
import analysis.numeric.IntValue

// the cmd property is extremely useful for debugging
@Suppress("unused")
/**
 * [range] is the maximum range of memory associated with this cell.
 * It has no coherent interpretation until the equivalence classes of [ConcreteAllocation]
 * stabilize, and [ConcreteAllocationManager.finalizeUnification] is called.
 *
 * Put another way, if you [unify] two [ConcreteAllocation] instances, their
 * [range] fields may not be the LUB of the [range] field values prior to unification.
 */
class ConcreteAllocation(private val cmd: CmdPointer, var range: IntValue) {

    /**
     * Ordinal that is assigned later by the unification process. All cells with the same unificand will be assigned the same
     * ordinal.
     */
    var ordinal: Int? = null

    /**
     * Unificand for this allocation site, or null if this is the representative site.
     */
    private var unificand: ConcreteAllocation? = null
    /**
     * Rank used to decide which unification to use, standard stuff here gang
     */
    private var rank: Int = 0

    fun find() : ConcreteAllocation {
        var retval = this
        while(retval.unificand != null) {
            retval = retval.unificand!!
        }
        return retval
    }

    fun unify(other: ConcreteAllocation) : ConcreteAllocation {
        val l = find()
        val r = other.find()
        return if(l !== r) {
            if(l.rank == r.rank) {
                l.rank++
            }
            if(l.rank > r.rank) {
                r.unificand = l
                l
            } else { // (l.rank < r.rank)
                l.unificand = r
                r
            }
        } else {
            l
        }
    }

    override fun toString(): String {
        return "ConcreteAllocation($cmd)"
    }
}

class ConcreteAllocationManager {
    enum class Sort {
        INPUT, OUTPUT, NONE
    }
    private val cache = mutableMapOf<Pair<CmdPointer, Sort>, ConcreteAllocation>()

    fun getConcreteAllocationForSite(where: LTACCmd, interval: IntValue, sort: Sort = Sort.NONE) : ConcreteAllocation {
        return cache.computeIfAbsent(where.ptr to sort) {
            ConcreteAllocation(where.ptr, interval)
        }.also {
            /**
             * Ensure that we record the widest possible range associated with this cell at all times.
             */
            it.range = it.range.join(interval)
        }
    }

    /**
     * Group the cells by the union/find representative, and assign each an ordinal. The ordinal is a stable "identity"
     * for the cell that is different than the interval of memory covered by the cell (which, as noted in the
     * documentation for [analysis.pta.ConcreteSpaceSet.ConcreteCell] can vary throughout program execution).
     *
     * Then the range covered by the equivalence class is computed by dating the join of all intervals associated with the
     * cells in the group.
     */
    fun finalizeUnification() {
        var ordinalUniverse = 0
        cache.values.groupBy {
            it.find()
        }.entries.forEach { (k, group) ->
            k.ordinal = ordinalUniverse++
            val totalRange = group.asSequence().map { it.range }.reduce(IntValue::join)
            group.forEach {
                it.range = totalRange
                it.ordinal = k.ordinal
            }
        }
    }
}
