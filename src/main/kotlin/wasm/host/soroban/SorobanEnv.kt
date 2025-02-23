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

@file:OptIn(ExperimentalSerializationApi::class)
package wasm.host.soroban

import datastructures.stdcollections.*
import kotlinx.serialization.*
import kotlinx.serialization.json.*
import utils.*
import wasm.host.soroban.modules.*

/**
    The deserialized contents of Soroban's env.json, which gives the names for all exported functions in the Soroban
    host.
 */
val sorobanEnv = Json.decodeFromStream<SorobanEnv>(
    SorobanEnv::class.java.classLoader.getResourceAsStream("soroban/env.json")
)

@KSerializable
class SorobanEnv(private val modules: List<SorobanModule>) {
    @Transient
    private val allModules = modules + CvtEnvModuleImpl.module

    @Transient
    val moduleExports = allModules.associateBy { it.export }

    @Transient
    val moduleExportsByName = allModules.associateBy { it.name }
}

@KSerializable
class SorobanModule(val export: String, val name: String, private val functions: List<SorobanFunction>) {
    @Transient
    val functionExports = functions.associateBy { it.export }

    @Transient
    val functionExportsByName = functions.associateBy { it.name }

    /** Gets the TAC implementation for this module */
    @Transient
    internal val impl = when(name) {
        "address" -> AddressModuleImpl
        "buf" -> BufModuleImpl
        "call" -> CallModuleImpl
        "context" -> ContextModuleImpl
        "crypto" -> CryptoModuleImpl
        "int" -> IntModuleImpl
        "ledger" -> LedgerModuleImpl
        "map" -> MapModuleImpl
        "prng" -> PrngModuleImpl
        "test" -> TestModuleImpl
        "vec" -> VecModuleImpl
        "env" -> CvtEnvModuleImpl // This is a special CVT-only module that doesn't have a Soroban implementation
        else -> error("Unknown Soroban module: $name")
    }
}

@KSerializable
class SorobanFunction(
    val export: String,
    val name: String,
    val args: List<SorobanArg>,
    @SerialName("return") val ret: SorobanType,
    val docs: String? = null,
    @SerialName("min_supported_protocol") val minSupportedProtocol: Int? = null,
    @SerialName("max_supported_protocol") val maxSupportedProtocol: Int? = null
)

@KSerializable
class SorobanArg(
    val name: String,
    val type: SorobanType
)

@KSerializable
enum class SorobanType {
    i64,
    u64,
    Bool,
    StorageType,
    @SerialName("Val") AnyVal,
    Void,
    Error,
    U32Val,
    I32Val,
    U64Val,
    I64Val,
    U128Val,
    I128Val,
    U256Val,
    I256Val,
    Symbol,
    I64Object,
    U64Object,
    TimepointObject,
    DurationObject,
    U128Object,
    I128Object,
    U256Object,
    I256Object,
    BytesObject,
    StringObject,
    SymbolObject,
    VecObject,
    MapObject,
    AddressObject,
}
