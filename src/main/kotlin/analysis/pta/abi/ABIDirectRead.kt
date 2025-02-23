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

package analysis.pta.abi

import allocator.Allocator
import allocator.GenerateRemapper
import allocator.GeneratedBy
import analysis.pta.ABICodeFinder
import analysis.pta.IDecoderAnalysis
import com.certora.collect.*
import tac.MetaKey
import utils.*
import vc.data.*

@KSerializable
@GenerateRemapper
@Treapable
data class ABIDirectRead(
    val output: TACSymbol.Var,
    val path: IDecoderAnalysis.DirectCalldataRead,
    @GeneratedBy(Allocator.Id.ABI, source = true)
    val id: Int
) : AmbiSerializable, TransformableVarEntityWithSupport<ABIDirectRead>, RemapperEntity<ABIDirectRead> {
    override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): ABIDirectRead {
        return ABIDirectRead(
            f(output), path.copy(
                bufferAccessPath = path.bufferAccessPath.transformVariables(f)
            ),
            id
        )
    }

    companion object {
        val META_KEY = MetaKey<ABIDirectRead>("abi.direct.read")
        val readFinder = object : ABIRangeFinder<ABICodeFinder.Source.Direct>() {
            override fun downcast(x: ABICodeFinder.Source): ABICodeFinder.Source.Direct? {
                return x as? ABICodeFinder.Source.Direct
            }
        }
    }

    override val support: Set<TACSymbol.Var>
        get() = path.bufferAccessPath.referencedVariables() + output
}
