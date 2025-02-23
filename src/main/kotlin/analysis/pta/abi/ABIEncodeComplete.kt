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
import utils.hashObject
import vc.data.RemapperEntity
import vc.data.TACSymbol
import vc.data.TransformableVarEntityWithSupport
import vc.data.UniqueIdEntity
import java.io.Serializable
import java.math.BigInteger
import datastructures.stdcollections.*

@Treapable
sealed class EncodeOutput : Serializable {
    object Scratch : EncodeOutput() {
        override fun hashCode() = hashObject(this)
        fun readResolve(): Any = Scratch
    }
    data class Alloc(val data: Set<TACSymbol.Var>) : EncodeOutput()
}

@Treapable
sealed class TopLevelValue : Serializable, UniqueIdEntity<TopLevelValue> {
    abstract fun transformVariables(f: (TACSymbol.Var) -> TACSymbol.Var) : TopLevelValue

    abstract val ty: HeapType

    data class Constant(val k: BigInteger) : TopLevelValue() {
        override val ty: HeapType
            get() = HeapType.Int

        override fun transformVariables(f: (TACSymbol.Var) -> TACSymbol.Var): TopLevelValue {
            return this
        }

        override fun mapId(f: (Any, Int, () -> Int) -> Int): TopLevelValue {
            return this
        }
    }

    data class Path(
        val paths: Set<ObjectPath>,
        override val ty: HeapType,
        val encodedPartitions: Map<PartitionField, EncodedPartitions>?
    ) : TopLevelValue(), UniqueIdEntity<TopLevelValue> {
        override fun transformVariables(f: (TACSymbol.Var) -> TACSymbol.Var): TopLevelValue {
            return Path(
                paths = paths.mapTo(mutableSetOf()) { it.transformVariables(f) },
                ty = ty,
                encodedPartitions = encodedPartitions
            )
        }

        override fun mapId(f: (Any, Int, () -> Int) -> Int): TopLevelValue {
            return Path(
                paths = paths,
                ty = ty,
                encodedPartitions = encodedPartitions?.mapValues { it.value.mapId(f) }
            )
        }
    }
}

@Treapable
data class EncodedBuffer(val buffer: Map<BigInteger, TopLevelValue>) : Serializable, UniqueIdEntity<EncodedBuffer> {
    fun transformVariables(f: (TACSymbol.Var) -> TACSymbol.Var) : EncodedBuffer {
        return EncodedBuffer(
            buffer = this.buffer.mapValues {
                it.value.transformVariables(f)
            }
        )
    }

    override fun mapId(f: (Any, Int, () -> Int) -> Int): EncodedBuffer {
        return EncodedBuffer(
            buffer = this.buffer.mapValues {
                it.value.mapId(f)
            }
        )
    }
}

@GenerateRemapper
@Treapable
data class ABIEncodeComplete(
    val target: EncodeOutput,
    val buffer: EncodedBuffer,
    val alignment: BigInteger,
    @GeneratedBy(Allocator.Id.ABI, source = true)
    val id: Int
) : Serializable, TransformableVarEntityWithSupport<ABIEncodeComplete>, RemapperEntity<ABIEncodeComplete> {
    companion object {
        val META_KEY = MetaKey<ABIEncodeComplete>("abi.encode.complete")

        val encodeFinder = object : ABIRangeFinder<ABICodeFinder.Source.Encode>() {
            override fun downcast(x: ABICodeFinder.Source): ABICodeFinder.Source.Encode? {
                return x as? ABICodeFinder.Source.Encode
            }
        }
    }

    override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): ABIEncodeComplete {
        return ABIEncodeComplete(
            target = when (target) {
                is EncodeOutput.Scratch -> EncodeOutput.Scratch
                is EncodeOutput.Alloc -> EncodeOutput.Alloc(
                    data = target.data.map(f).toSet()
                )
            },
            buffer = buffer.transformVariables(f),
            id = this.id,
            alignment = alignment
        )
    }

    override val support: Set<TACSymbol.Var>
        get() {
            val toRet = mutableSetOf<TACSymbol.Var>()
            this.target.let { it as? EncodeOutput.Alloc }?.data?.let(toRet::addAll)
            buffer.buffer.values.forEach {
                (it as? TopLevelValue.Path)?.paths?.forEach {
                    when(val r = it.root) {
                        is ObjectPathAnalysis.ObjectRoot.V -> toRet.add(r.v)
                        is ObjectPathAnalysis.ObjectRoot.CalldataRoot -> toRet.addAll(r.bp.referencedVariables())
                    }
                }
            }
            return toRet
        }
}
