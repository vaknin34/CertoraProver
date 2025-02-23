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

import java.util.*

class DynamicBitVectorUniverse<T: Any> : IBitVectorUniverse<T> {
    private val bw : ArrayList<T> = arrayListOf<T>()
    private val fw : MutableMap<T, Int> = mutableMapOf()

    override fun lookup(x: T): Int {
        return fw.computeIfAbsent(x) {
            val ind = bw.size
            bw.add(it)
            check(ind == bw.lastIndex)
            ind
        }
    }

    override fun lookup(x: Int): T {
        if(x > bw.lastIndex) {
            throw IllegalArgumentException("$x does not correspond to an allocated number")
        }
        return bw[x]
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