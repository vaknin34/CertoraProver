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

package spec.converters

import spec.SafeMathCodeGen
import spec.cvlast.abi.DataLayout
import spec.cvlast.typedescriptors.TerminalAction
import spec.cvlast.typedescriptors.TerminalAction.Companion.sizeAsEncodedMember as shadowedSizeAsEncodedMember
import java.math.BigInteger

interface DataLayoutInterpreter : SafeMathCodeGen {
    fun <O, S: Any, D: Any> DataLayout.TupleOf<TerminalAction<O, S, D, *>>.offsetOfField(ind: Int) : BigInteger {
        return this.elements.asSequence().take(ind).fold(BigInteger.ZERO) { acc, e ->
            acc + e.second.shadowedSizeAsEncodedMember()
        }
    }

    companion object {
        fun <O, S: Any, D: Any> DataLayout<TerminalAction<O, S, D, *>>.sizeAsEncodedMember(): BigInteger {
            return this.shadowedSizeAsEncodedMember()
        }
    }
}
