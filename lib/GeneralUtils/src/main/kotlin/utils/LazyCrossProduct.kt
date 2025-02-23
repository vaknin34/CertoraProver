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

package utils

/**
 * Computes the cross (cartesian) product over the given list of lists.
 * Lazily computes only the next tuple for each call of [next], so shouldn't explode in space.
 */
class LazyCrossProduct<T>(val listList: List<List<T>>) : Iterator<List<T>> {
    /** Compute tuples of length [tupleLength] over elements of the list [list]. */
    constructor(list: List<T>, tupleLength: Int) : this(Array(tupleLength) { _ -> list }.toList())

    private val tupleLength = listList.size

    private val currentPointer = Array(tupleLength) { _ -> 0 }.toMutableList()
    private var hasNext = listList.all { it.isNotEmpty() }
    private val currentTuple: MutableList<T> =
        if (!hasNext) {
            mutableListOf()
        } else {
            val res = mutableListOf<T>()
            for (i in 0 until tupleLength) {
                res.add(listList[i][0])
            }
            res
        }
    private var isFirst = true

    /** Precomputed number of times that [next] will succeed. */
    val sizeOfIterator = listList.fold(1) { acc, l -> acc * l.size }

    override fun hasNext(): Boolean = hasNext

    override fun next(): List<T> {
        if (!hasNext()) {
            throw NoSuchElementException()
        }
        if (isFirst) {
            isFirst = false
            return currentTuple
        }
        incrementPointer()
        return currentTuple
    }

    private fun incrementPointer() {
        var carry = true

        for (i in 0 until tupleLength) {
            val maxDigit = listList[i].size - 1
            if (carry && currentPointer[i] == maxDigit) {
                currentPointer[i] = 0
                currentTuple[i] = listList[i][0]
                // carry stays true
            } else if (carry && currentPointer[i] != maxDigit) {
                val inc = currentPointer[i] + 1
                currentPointer[i] = inc
                currentTuple[i] = listList[i][inc]
                carry = false
            } else {
                /* carry was false, nothing to do */
                break
            }
        }
        if (carry) hasNext = false
    }

}
