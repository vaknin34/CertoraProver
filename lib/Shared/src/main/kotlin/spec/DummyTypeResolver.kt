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

@file:UseSerializers(BigIntegerSerializer::class)
package spec

import kotlinx.serialization.UseSerializers
import spec.cvlast.CVLType
import spec.cvlast.CurrentContract
import spec.cvlast.EVMBuiltinTypes
import spec.cvlast.SolidityContract
import spec.cvlast.typedescriptors.FromVMContextDispatcher
import spec.cvlast.typedescriptors.ITypeDescriptorConverter
import spec.cvlast.typedescriptors.ToVMContextDispatcher
import spec.cvlast.typedescriptors.VMTypeDescriptor
import utils.BigIntegerSerializer
import utils.CollectingResult
import utils.CollectingResult.Companion.asError
import utils.CollectingResult.Companion.lift
import utils.KSerializable
import java.math.BigInteger

/**
 * @property primaryContract the canonical name of the currentContract
 */
class DummyTypeResolver(private val primaryContract: SolidityContract) : AbstractTypeResolver() {
    init {
        contractAliases[CurrentContract.name] = primaryContract.name
    }
    @KSerializable
    sealed interface DummyTypeDescriptor : VMTypeDescriptor {
        override fun <O, SRC, DST> converterFrom(
            fromType: CVLType.PureCVLType,
            i: ToVMContextDispatcher<O, SRC, DST>,
        ): CollectingResult<ITypeDescriptorConverter<O, SRC, DST>, String> {
            return "The dummy type resolver doesn't support type conversions".asError()
        }

        override fun <O, SRC, DST> converterTo(
            toType: CVLType.PureCVLType,
            i: FromVMContextDispatcher<O, SRC, DST>,
        ): CollectingResult<ITypeDescriptorConverter<O, SRC, DST>, String> {
            return "The dummy type resolver doesn't support type conversions".asError()
        }

        override fun mergeWith(other: VMTypeDescriptor): CollectingResult<VMTypeDescriptor, String> {
            return "merging not supported for the dummy type resolver".asError()
        }
    }

    @KSerializable
    data class ContractTypeIdentifier(val contract: String?, val id: String, val location: String?): DummyTypeDescriptor
    @KSerializable
    data class StaticArrayType(val base: VMTypeDescriptor, val size: BigInteger, val location: String?) : DummyTypeDescriptor
    @KSerializable
    data class MappingType(val key: VMTypeDescriptor, val value: VMTypeDescriptor, val location: String?) : DummyTypeDescriptor
    @KSerializable
    data class ArrayType(val base: VMTypeDescriptor, val location: String?) : DummyTypeDescriptor

    override val factory: VMDescriptorFactory
        get() = object : VMDescriptorFactory {
            override fun getDynamicArray(location: String?, vmBase: VMTypeDescriptor): VMTypeDescriptor {
                return ArrayType(
                    vmBase, location
                )
            }

            override fun getMappingType(kRes: VMTypeDescriptor, vRes: VMTypeDescriptor, location: String?): VMTypeDescriptor {
                return MappingType(
                    location = location,
                    value = kRes,
                    key = vRes
                )
            }

            override fun getStaticArray(resolveIn: VMTypeDescriptor, location: String?, n: BigInteger): VMTypeDescriptor {
                return StaticArrayType(base = resolveIn, location = location, size = n)
            }

            override fun methodType(): CVLType.PureCVLType {
                return EVMBuiltinTypes.method // this is still weirdly part of this interface???
            }

        }

    override fun resolveVMType(contractName: String?, typeName: String, location: String?): CollectingResult<VMTypeDescriptor, String> {
        return ContractTypeIdentifier(
            location = location,
            id = typeName,
            contract = contractName?.let(this::resolveContractName)
        ).lift()
    }

    override fun validContract(contractName: String): Boolean {
        return true
    }

    override fun resolveCVLTypeWithContract(contract: String, id: String): CollectingResult<CVLType.PureCVLType, String> {
        val con = this.resolveContractName(contract)
        return CVLType.PureCVLType.Sort("$con.$id").lift()
    }

    override fun clone(): TypeResolver {
        return DummyTypeResolver(primaryContract).also {
            it.contractAliases.putAll(this@DummyTypeResolver.contractAliases)
        }
    }

}
