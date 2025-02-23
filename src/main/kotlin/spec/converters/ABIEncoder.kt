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

import spec.converters.repr.WithCVLProgram
import spec.cvlast.typedescriptors.IConverterOutput
import spec.cvlast.typedescriptors.IExternalEncodeOutput
import vc.data.CVLTACProgram
import vc.data.TACSymbol

/**
 * An object that represents a "terminal" operation of abi encoding. In particular, this class indicates
 * that (some) encoding is complete, and the new position of the output pointer is in the variable [outputPointer]
 */
interface WithOutputPointer {
    val outputPointer: TACSymbol.Var
}

/**
 * The result of encoding that produces some [code] which is the result of the encoding, and an object [outputPosition]
 * that represents the buffer state post encoding, specifically the variable which holds the current position in the
 * output buffer via the [WithOutputPointer.outputPointer] field. This exists to interop with the opaque [IConverterOutput]
 * interface and ABIEncoders.
 */
data class EncoderOutput(
    val outputPosition: WithOutputPointer,
    val code: CVLTACProgram
) : IExternalEncodeOutput, WithOutputPointer by outputPosition, WithCVLProgram<EncoderOutput> {
    override fun mapCVLProgram(f: (CVLTACProgram) -> CVLTACProgram): EncoderOutput {
        return this.copy(code = f(this.code))
    }


}

fun IConverterOutput.lower() : Pair<WithOutputPointer, CVLTACProgram> = (this as EncoderOutput).let {
    it.outputPosition to it.code
}
/**
 * Lift this pair into the embedding into [IConverterOutput] (we can't have this particular instantiation of the
 * Pair type implement [IConverterOutput] alas
 */
fun <T: WithOutputPointer> Pair<T, CVLTACProgram>.lift() = EncoderOutput(this.first, this.second)
