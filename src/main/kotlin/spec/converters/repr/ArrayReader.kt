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
 * Interface for reading array elements. There are three modes:
 * 1. Reading a specific element ([readElem])
 * 2. Iterating over all elements up to some bound ([foreachElem])
 * 3. Getting a [TACCmd.CVL.BufferPointer] to the array
 *
 * In cases 1 and 2, the elements are themselves accessed with [CVLDataInput].
 *
 * As with the other readers and writers, the callbacks are expected to return some code that "does something"
 * with the contents of the array; the results of these callbacks is the joined with code that effects
 * the access in question and then returned from the overall result.
 */
interface ArrayReader {
    /**
     * Generate an unrolled loop. For [ArrayReader] objects for reading static arrays,
     * bound of the loop will the length of the static loop, otherwise the bound is the value of [config.Config.LoopUnrollConstant].
     *
     * The callback [f] is called for each unrolled iteration; the first parameter is the iteration number/element index, and
     * the second argument is the input "pointing to" that element. [f] is not necessarily *called* in "iteration order",
     * but the unrolling is performed so that iteration happens sequentially, i.e., the code returned by `f(0, _)` definitely
     * executes before the code returned by `f(1, _)` and so on.
     *
     * Note that [f] does **not** need to do any bounds checking, that is handled by the [ArrayReader] object.
     *
     * In pseudo-code, this function returns a program with the following structure:
     * ```
     * if(0 < len) {
     *     <f(0, readElem(0))>
     *     if(1 < len) {
     *        <f(1, readElem(1))>
     *        if(2 < len) ...
     *     }
     * }
     * ```
     */
    fun foreachElem(f: (Int, CVLDataInput) -> CVLTACProgram) : CVLTACProgram

    /**
     * Read element with logical index [i], passing the [CVLDataInput] pointing to this element to [f]. The code
     * to effect the access is prepended onto the returned value [R] via [WithCVLProgram.mapCVLProgram]
     */
    fun <R: WithCVLProgram<R>> readElem(i: Int, f: (CVLDataInput) -> R) : R

    /**
     * Read element with logical index [idx], passing the [CVLDataInput] pointing to this element to [f].
     * The code to effect the access is prepended onto the returned value [R] via [WithCVLProgram.mapCVLProgram].
     */
    fun <R: WithCVLProgram<R>> readElem(idx: TACSymbol, f: (CVLDataInput) -> R) : R

    /**
     * Construct a [TACCmd.CVL.BufferPointer] which references the location of this array's contents and pass
     * that through to [f]. The code to effect construct the [TACCmd.CVL.BufferPointer] object is prepended
     * to the result of [f].
     * It is NOT checked that this array is safe to perform a long-copy from (i.e., it's elements are value types).
     */
    fun toOutput(f: (TACCmd.CVL.BufferPointer) -> CVLTACProgram) : CVLTACProgram
}
