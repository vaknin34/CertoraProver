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

@file:kotlinx.serialization.UseSerializers(utils.BigIntegerSerializer::class)
package analysis.pta.abi

import allocator.Allocator
import allocator.GenerateRemapper
import allocator.GeneratedBy
import analysis.pta.ABICodeFinder
import analysis.pta.HeapType
import com.certora.collect.*
import tac.MetaKey
import utils.*
import vc.data.*
import java.math.BigInteger

@KSerializable
@GenerateRemapper
@Treapable
/**
 * Representation of the completion of an ABI decode operation
 *
 * @property sourceBuffer the buffer from which we've completed decoding
 * @property sourcePath the location the source buffer that points to the object we've decoded
 * @property output points to the decoded object
 * @property fieldPointers each (p, off) in [fieldPointers] is a variable defined _during_ the decoding
 *           as pointing to the output object + offset `off`.
 *           This exists in service of the direct inlining optimization: if we slice out the decoding code,
 *           we may slice out the definitions of the variables in [fieldPointers] -- if they're still live,
 *           then that's an issue. We record enough information here so that they can be redefined in terms of
 *           the output variables
 * @property decodedType the type of the decoded object
 */
data class ABIDecodeComplete(
    val sourceBuffer: TACSymbol.Var,
    val sourcePath: DecoderAnalysis.BufferAccessPath,
    val output: Set<TACSymbol.Var>,
    val fieldPointers: Set<Pair<TACSymbol.Var, BigInteger>>,
    val decodedType: HeapType,
    @GeneratedBy(Allocator.Id.ABI, source = true)
    val id: Int,
    val fieldRelations: Map<PartitionField, EncodedPartitions>?
) : AmbiSerializable, TransformableVarEntityWithSupport<ABIDecodeComplete>, RemapperEntity<ABIDecodeComplete> {

    companion object {
        val META_KEY = MetaKey<ABIDecodeComplete>("pta.abi.decode")

        val decodeFinder = object : ABIRangeFinder<ABICodeFinder.Source.Decode>() {
            override fun downcast(x: ABICodeFinder.Source): ABICodeFinder.Source.Decode? {
                return x as? ABICodeFinder.Source.Decode
            }
        }
    }

    override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): ABIDecodeComplete {
        return ABIDecodeComplete(
            sourceBuffer = f(sourceBuffer),
            sourcePath = this.sourcePath.transformVariables(f),
            output = this.output.map(f).toSet(),
            decodedType = decodedType,
            fieldPointers = this.fieldPointers.map { (x, o) -> f(x) to o }.toSet(),
            id = this.id,
            fieldRelations = this.fieldRelations
        )
    }

    override val support: Set<TACSymbol.Var> get() = this.output + this.sourceBuffer + sourcePath.referencedVariables()
}
