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
import spec.cvlast.typedescriptors.ICVLDataInput
import tac.CallId
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * A common class for accessing/reading data in CVL (the `input` in the name
 * suggests that this type is used to get the "input" to some operation). This interface papers over the
 * fact that we use different representations for types depending on whether those types appear
 * within an array or not. Instead, the main 4 "shapes" of types (struct, static arrays, dynamic arary,
 * and primitive) are all accessed according to the member functions here. Types nested within other types
 * are handled by several of these operations themselves returning more [CVLDataInput] instances; indicating
 * how to read the member of, e.g., a struct field, or member of an array. This interface does not allow for
 * introspection of the data being accessed; it is assumed that the user of this class has some other information
 * about what kind of data is being accessed, and uses that to determine which of the member functions is called.
 * In practice, this extra information is always available where this class would be used, and thus we chose
 * this representation instead of, e.g., a sealed interface that has to be switched over to expose the correct type.
 * Thought of another way, the [struct], [dynamicArray], and other accessors themselves switch over the representation
 * internally, throwing an error if the input doesn't have the correct shape, or performing the access; which effectively
 * is what the "downcast to the correct type and access" approach would always do.
 *
 * With that said, this interface attempts best effort type checking, but makes no *guarantees* to throw if the data being
 * accessed is not of the correct shape. However, as noted above, it is expected that these types are always traversed
 * with some other information which "guarantees" that the correct accessors are called.
 *
 *  All [CVLDataInput] carry with them a [context] (via the [ProgramGenMixin]) which describes the compilation context.
 *  This determines the call index to use during code generation, and this is passed through to some of the callbacks.
 *  It is expected (but not checked) that the callbacks that receive this context will use it for generating the output
 *  of these functions.
 */
interface CVLDataInput : ProgramGenMixin, ICVLDataInput {
    /**
     * Interpret the current input as a struct, returning a [StructReader] class for reading the individual fields.
     * If the input does not appear to be a struct, this function will throw an exception. Note that this function,
     * unlike all the other accessors in this class, returns a class instead of passing it through to a callback.
     * It turns out this is far more convenient for the common uses of the struct case, whereby some "writer" will
     * loop over all field of a struct, and this provides an easy way to support those accesses "on demand".
     */
    fun <R: WithCVLProgram<R>> struct() : StructReader<R>

    /**
     * Interpret the current input as a static array of length [len], throwing an exception if the current
     * type does not appear to be a static array or if [len] is not correct. Otherwise, it passes
     * an [ArrayReader] for reading the elements of this array to the callback [f]. The type [R] returned
     * from that callback has code required to effect the access prepended onto it (via [WithCVLProgram.mapCVLProgram])
     * and is then returned from this function.
     */
    fun <R: WithCVLProgram<R>> staticArray(len: BigInteger, f: (ArrayReader) -> R) : R

    /**
     * Interpret the current input as a dynamic array, and throw an exception if the current input does not appear
     * to be an array. Otherwise, calls [callBack] with three arguments: a variable which holds
     * the dynamic length of the array, the [spec.CVLCompiler.CallIdContext] of the input, and a [ArrayReader]
     * to access the elements of this array. The result of [callBack] has the code required to effect the access
     * (e.g., reading the dynamic length) prepended onto it (via [WithCVLProgram.mapCVLProgram]) and is then returned.
     */
    fun <R: WithCVLProgram<R>> dynamicArray(
        callBack: (dynamicLengthVar: TACSymbol.Var, context: CVLCompiler.CallIdContext, reader: ArrayReader) -> R
    ) : R

    /**
     * Interpret the current input as a primitive value, bind it to a variable, and then pass that value to [f] along
     * with the context. The result of [f] has the code to effect the access (e.g., reading the primitive value
     * out of a buffer) prepended to it (via [WithCVLProgram.mapCVLProgram]) and is then returned.
     */
    fun <R: WithCVLProgram<R>> readPrimitive(f: (TACSymbol.Var, CVLCompiler.CallIdContext) -> R) : R

    companion object {
        operator fun invoke(v: TACSymbol.Var, callId: CallId) = CVLDirectInput(
            s = v,
            context =  callId.toContext()
        )
    }
}
