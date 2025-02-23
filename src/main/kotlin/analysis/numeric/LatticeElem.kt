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

package analysis.numeric

import com.certora.collect.*

interface LatticeElem<in In, out Out> {
    fun widen(next: In) : Out
    fun join(other: In) : Out
}

fun <K, I: LatticeElem<I, I>> TreapMap<K, I>.join(other: TreapMap<K, I>, top: I): TreapMap<K, I> {
    return this.merge(other) { _, left, right ->
        (left ?: top).join(right ?: top)
    }
}

fun <K, I: LatticeElem<I, I>> TreapMap<K, I>.widen(next: Map<K, I>, top: I): TreapMap<K, I> {
    return this.merge(next) { _, left, right ->
        (left ?: top).widen(right ?: top)
    }
}
