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

import vc.data.TACSymbol
import java.math.BigInteger

sealed class BufferPointer : WithOutputPointer {
    /**
     * [x] is the (absolute) position within the buffer, with the symbolic position given in [outputPointer]
     */
    data class Constant(val x: BigInteger, override val outputPointer: TACSymbol.Var) : BufferPointer() {
        override fun addTo(amount: BigInteger, newSym: TACSymbol.Var): BufferPointer {
            return Constant(x + amount, newSym)
        }
    }

    data class Symbol(override val outputPointer: TACSymbol.Var, val relativeOffset: BigInteger?) : BufferPointer() {
        override fun addTo(amount: BigInteger, newSym: TACSymbol.Var): BufferPointer {
            return Symbol(newSym, relativeOffset = relativeOffset?.plus(amount))
        }

    }

    /**
     * Return a new [BufferPointer] buffer pointer, which is adding [amount] to this,
     * with the result being held in [newSym]
     */
    abstract fun addTo(amount: BigInteger, newSym: TACSymbol.Var): BufferPointer

    /**
     * The variable which points to a position in the buffer.
     */
    abstract override val outputPointer: TACSymbol.Var

    companion object {
        operator fun invoke(o: WithOutputPointer): BufferPointer {
            return if (o is BufferPointer) {
                o
            } else {
                Symbol(o.outputPointer, null)
            }
        }
    }
}
