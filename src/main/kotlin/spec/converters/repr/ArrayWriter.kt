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

package spec.converters.repr

import vc.data.CVLTACProgram
import vc.data.TACCmd
import vc.data.TACSymbol

/**
 * Dual of [ArrayReader], used for filling in elements of an array. Used for both static and dynamic arrays. This class
 * is not responsible for writing the length of the array; that is handled by the creators of this class.
 *
 * As CVL does not allow writing into array, this is **only** used for initialization, which is why there is no
 * corresponding function for [ArrayReader.readElem]; it never makes sense to write only one element. In other words,
 * arrays can only be initialized by long copying values into them (via [longCopy]) or by initializing each element
 * (with [foreachElem]).
 */
interface ArrayWriter {
    /**
     * Convenience function where [src] is expected to be a bytemap that originates from the EVM. Simply constructs the
     * Appropriate [TACCmd.CVL.BufferPointer] and calls [longCopy].
     */
    fun longCopy(src: TACSymbol.Var, srcOffset: TACSymbol) : CVLTACProgram = longCopy(TACCmd.CVL.BufferPointer(offset = srcOffset, buffer = TACCmd.CVL.Buffer.EVMBuffer(src)))

    /**
     * Long copy the contents of [pointer] into this variable. As in the [ArrayReader] case, this is not guaranteed to throw
     * if it is not safe to long copy elements into this array (i.e., this array has value type elements). Note that the
     * length of the source array does not appear, it is assumed (but again, not checked) that the array being referenced
     * by [pointer] has the same length as this array (which is stored by the current implementation).
     */
    fun longCopy(pointer: TACCmd.CVL.BufferPointer) : CVLTACProgram

    /**
     * Correspondence for [ArrayReader.foreachElem]. As there, the unrolled loop has a bound determined by the
     * source of this [ArrayWriter]: for static arrays, it is the static size; for dynamic arrays, the iteration
     * is bounded by [config.Config.LoopUnrollConstant]. As with that function [f] is given the iteration number/element index,
     * and the [CVLDataOutput] for writing that element; the program returned is expected to initialize that element.
     * [f] is **not** responsible for bounds checking, that is handled by this interface.
     */
    fun foreachElem(f: (Int, CVLDataOutput) -> CVLTACProgram) : CVLTACProgram
}
