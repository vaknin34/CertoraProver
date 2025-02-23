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

import spec.CVLCompiler
import spec.CVLCompiler.CallIdContext.Companion.toContext
import spec.ProgramGenMixin
import spec.cvlast.typedescriptors.ICVLDataOutput
import tac.CallId
import vc.data.CVLTACProgram
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * The dual of [CVLDataInput] but for writing CVL values (i.e., this class is to be used
 * for the "output" of some operation). Note that the choice of who gets a callback and who gets a writer
 * is switched: [startStruct] expects a writer and returns a program, whereas [startStaticArray] and [startDynamicArray]
 * give back a writer. This "matches up" with how we expect [CVLDataInput] to be used, when moving data from one CVL
 * location to another, we expect the [ArrayWriter] returned by the start array variants to be captured and then used in
 * the callbacks for [CVLDataInput.staticArray] and [CVLDataInput.dynamicArray]. Similarly, we expect the
 * [StructReader] returned by [CVLDataInput.struct] to be captured and used in the body of [StructWriter].
 *
 * All of the caveats and justifications for the design of [CVLDataInput] apply here:
 * there is a best effort to check that the shape of the output matches the operations call on this interface but nothing
 * is guaranteed.
 */
interface CVLDataOutput : ProgramGenMixin, ICVLDataOutput {

    /**
     * Interpret this output "location" as a struct, and populate its field using [structWriter]. If the output location
     * is not a struct, this function throws. The values
     * of each struct field here are provided by calling [StructWriter.generateField], passing in a [CVLDataOutput]
     * corresponding to the for the struct field. The order that [structWriter]'s [StructWriter.generateField]
     * is called is not specified, but [StructWriter.generateField] will be called exactly once for each struct
     * field for this output. After the individual struct fields are populated, this code is merged together with
     * the code to effect the construction of the struct itself.
     */
    fun startStruct(structWriter: StructWriter): CVLTACProgram

    /**
     * Interpret this output location as a static array with size [len]. If the output location is not a static array,
     * or is of different size than [len], this function throws. Otherwise, this function returns an [ArrayWriter]
     * for populating the elements of the static array. See that class for details.
     */
    fun startStaticArray(len: BigInteger) : ArrayWriter

    /**
     * Interpret this output location as a dynamic array, whose length is [len]. If the output location is not a dynamic
     * array, this function throws. Otherwise, this function returns an [ArrayWriter] to populating the elements of the array.
     * Note that the implementations of the returned [ArrayWriter] **will** set the length fields accordingly.
     */
    fun startDynamicArray(len: TACSymbol) : ArrayWriter

    /**
     * Interpret this output location as a primitive value, throwing if this does not appear to the be case.
     * [f] receives a variable name to which the primitive value should be written, as well as the
     * [context] that the resulting program should use. [f] is expected to return a program that
     * moves the primitive value into the variable. The code that performs this move is then prepended onto code
     * that moves the primitive variable into its final location; if the primitive is in a struct within an array
     * this involves writing the (newly populated) temporary value into a buffer.
     */
    fun movePrimitive(f: (TACSymbol.Var, CVLCompiler.CallIdContext) -> CVLTACProgram) : CVLTACProgram

    companion object {
        operator fun invoke(v: TACSymbol.Var, id: CallId) = CVLDirectOutput(context = id.toContext(), tgt = v)
    }
}
