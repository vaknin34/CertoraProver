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

package analysis.bitvector

import utils.uncheckedAs
import java.util.*

class StaticBitVectorUniverse<T: Any>(x: Iterable<T>) : IBitVectorUniverse<T> {
    private val bw: Array<Any>
    private val fw: Map<T, Int>

    init {
        val d = x.toList()
        val i = d.size
        bw = Array<Any>(i) {
            d[it]
        }
        val m = mutableMapOf<T, Int>()
        for(ind in bw.indices) {
            m[bw[ind].uncheckedAs<T>()] = ind
        }
        fw = m
    }

    override fun lookup(x: T) : Int = fw[x] ?: error("$x not in universe")

    override fun lookup(x: Int) : T {
        return bw[x].uncheckedAs<T>()
    }

    override fun asVec(x: Iterable<T>) : BitSet {
        val bs = BitSet(bw.size)
        for(t in x) {
            bs.set(lookup(t))
        }
        return bs
    }

    override fun singleton(x: T) : BitSet {
        val bs = BitSet(bw.size)
        bs.set(lookup(x))
        return bs
    }
}
