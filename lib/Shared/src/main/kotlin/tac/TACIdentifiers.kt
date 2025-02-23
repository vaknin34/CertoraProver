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

package tac

import datastructures.stdcollections.*

object TACIdentifiers {
    const val callIndexPrefix = "@"
    const val tagPrefix = ":"

    // We validate identifiers enough that using a Regex is a serious performance issue.  Instead, we precompute a
    // couple of arrays that we can use to check if a character is allowed in the first position of an identifier, or
    // subsequent positions, and then we just check each character in the identifier against the appropriate array.
    private fun allow(chars: List<Char>) = chars.toSet().let { set ->
        BooleanArray(Char.MAX_VALUE.code + 1) { it.toChar() in set }
    }

    private val allowedFirstChars = allow(('A'..'Z') + ('a'..'z') + '_')
    private val allowedRemainingChars = allow(('A'..'Z') + ('a'..'z') + '_' + '!' + '$' + '.' + ('0'..'9'))

    fun valid(id: String): Boolean {
        if (id.length == 0) {
            return false
        }
        if (!allowedFirstChars[id[0].code]) {
            return false
        }
        for (i in 1..id.lastIndex) {
            if (!allowedRemainingChars[id[i].code]) {
                return false
            }
        }
        return true
    }
}


