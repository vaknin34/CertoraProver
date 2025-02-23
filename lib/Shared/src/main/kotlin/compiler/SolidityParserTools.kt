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

package compiler

import bridge.Method
import bridge.types.PrimitiveType
import bridge.types.SolidityTypeDescription
import bridge.types.SolidityTypeInstance
import bridge.types.StructTypeMemberType
import compiler.JumpType.Companion.toJumpType
import kotlinx.serialization.Serializable
import log.*
import spec.cvlast.typedescriptors.PrintingContext
import java.math.BigInteger

private val logger = Logger(LoggerTypes.COMMON)


fun parseSrcMapping(srcMap : String) : List<SrcMapping> {
    fun convertFull(i : String, last : SrcMapping?) : SrcMapping {

        val _components = i.split(":")
        if (last == null &&  _components.size < 4) {
            throw Exception("Invalid srcmap starting with $i (should have at least 4 components separated by ':'")
        }
        val components = _components.take(4) // ignoring new components, e.g. as in solidity 6 "modifier depth" - which is the 5th component
        if (last == null && components.size != 4) {
            throw Exception("Invalid srcmap starting with $i (should have 4 components separated by ':'")
        } else if (last == null) {
            logger.debug { "Handling srcmap string $i (components=$components size ${components.size}) without last"}
            return SrcMapping(components.get(2).toInt(),components.get(0).toInt(), components.get(1).toInt(), components.get(3).toJumpType())
        }

        logger.debug{"Handling srcmap string $i (components=$components size ${components.size}) with last $last"}
        return when (components.size) {
            0 -> last
            1 -> if (components.get(0).isBlank()) {
                last
            } else {
                SrcMapping(
                        last.source,
                        components.get(0).toInt(),
                        last.len,
                        last.jumpType
                )
            }
            2 -> SrcMapping(
                    last.source,
                    components.get(0).toIntOrNull()?:last.begin,
                    components.get(1).toInt(),
                    last.jumpType
            )
            3 -> SrcMapping(
                    components.get(2).toInt(),
                    components.get(0).toIntOrNull()?:last.begin,
                    components.get(1).toIntOrNull()?:last.len,
                    last.jumpType
            )
            4 -> SrcMapping(
                    components.get(2).toIntOrNull()?:last.source,
                    components.get(0).toIntOrNull()?:last.begin,
                    components.get(1).toIntOrNull()?:last.len,
                    components.get(3).toJumpType()
            )
            else -> throw Exception("Invalid srcmap string $i with more than 4 components")
        }
    }

    val perInstruction = srcMap.split(";")
    if (perInstruction.size == 0 || (perInstruction.size == 1 && perInstruction.first().trim().isBlank())) {
        return listOf()
    }

    val first = perInstruction.first()
    var last : SrcMapping? = null
    val retList = mutableListOf<SrcMapping>()
    last = convertFull(first,last)
    retList.add(last)
    perInstruction.drop(1).forEach { i ->
        last = convertFull(i, last)
        retList.add(last!!)
    }

    return retList
}

fun parseVariableMapping(varMap : String) : List<VariableMapping> {
    val perInstruction = varMap.split(";")
    if (perInstruction.isEmpty() || (perInstruction.size == 1 && perInstruction.first().trim().isBlank())) {
        return listOf()
    }

    return perInstruction
            .map { mapping ->
                when {
                    mapping.isEmpty() -> mapOf()
                    else -> {
                        mapping.split(",")
                                .map {
                                    val list = it.split(":")
                                    when {
                                        list.isEmpty() -> null
                                        list.size == 2 -> Pair(list[0], list[1])
                                        else -> throw Exception("malformed variable mapping: $mapping, " +
                                                "should have exactly 2 elements at $it")
                                    }
                                }
                                .filterNotNull()
                                .associateBy( { it.first },
                                        { it.second.toInt() })
                    }
                }

            }
}


// ABI related

/**
 * Serialization class of the ABI produced either by solc or recomputed information when loading bytecode from
 * EtherScan via our https://github.com/Certora/BytecodeFetcher
 *
 * @param selector If not null, and the ABI entry is a function, this contains the sighash of the function (as hex value starting with 0x).
 * @param type The type of the abi encoded entry. Can also be event, constructor, or fallback
 */
@Serializable
data class ABI(val constant: Boolean = false,
               val inputs : List<ABIComponent> = listOf(),
               val name : String = "",
               val outputs: List<ABIComponent> = listOf(),
               val payable : Boolean = false,
               val stateMutability : SolidityFunctionStateMutability = SolidityFunctionStateMutability.Default, // TODO: Check default - did not find
               val type : String = "function",
               val selector : String? = null,
               val anonymous : Boolean = false) {
    fun toCanonicalSig(assumeLibrary: Boolean = false): String {
        return inputs.map {
            it.toSolidityType()
        }.joinToString(",", prefix = "$name(", postfix = ")") {
            it.toVMTypeDescriptor().canonicalString(object : PrintingContext {
                override val isLibrary: Boolean
                    get() = assumeLibrary
            })
        }
    }

    fun toMethod(sighash: String): Method =
        Method(
            name = this.name,
            isEnvFree = false,
            isConstant = this.constant,
            stateMutability = this.stateMutability,
            notpayable = !this.payable,
            sighash = sighash,
            fullArgs = this.inputs.map { it.toSolidityType() },
            returns = this.outputs.map { it.toSolidityType() },
            isLibrary = false,
            contractName = ""
        )

}

@Serializable
data class ABIComponent(val name : String,
                        val type : String,
                        val indexed : Boolean = false,
                        val components : List<ABIComponent> = listOf(),
                        val internalType : String? = null) {
    fun toCanonicalString() : String {
        if(components.isEmpty()) {
            return type
        }
        assert(type.startsWith("tuple"))
        val arraySuffix = type.removePrefix("tuple")
        return "(${components.joinToString(",") { it.toCanonicalString() }})$arraySuffix"
    }

    @Suppress("AvoidProblematicStringFunctions")
    private fun parseInternalName(s: String) : SolidityTypeDescription {
        if(s.endsWith("]")) {
            val arrayDimMatcher = "\\[(\\d+)?]$".toRegex()
            val m = arrayDimMatcher.find(s) ?: throw IllegalArgumentException("Expected array like type $s, but did not match")
            if(m.groups.get(1) != null) {
                val staticSize = BigInteger(m.groups.get(1)!!.value, 10)
                return parseInternalName(s.substring(0, m.range.first)).let { baseType ->
                    SolidityTypeDescription.StaticArray(
                        staticArraySize = staticSize,
                        staticArrayBaseType = baseType
                    )
                }
            } else {
                check(m.groups.get(0)!!.value == "[]") {
                    "Unexpected match result for $s: ${m.groupValues}"
                }
                return parseInternalName(s.substring(0, m.range.first)).let {
                    SolidityTypeDescription.Array(
                        dynamicArrayBaseType = it
                    )
                }
            }
        } else if(s.startsWith("enum ")) {
            return SolidityTypeDescription.Primitive(PrimitiveType.uint8)
        } else if(s.startsWith("contract ") || s.startsWith("address")) {
            return SolidityTypeDescription.Primitive(PrimitiveType.address)
        } else if(s.startsWith("struct ")) {
            val structName = s.substring("struct ".length)
            val (contract, baseName) = structName.split('.').let {
                if(it.size == 2) {
                    it[0] to it[1]
                } else {
                    check(it.size == 1) {
                        "Unexpected number of components for struct type $s: $it"
                    }
                    null to it[0]
                }
            }
            return SolidityTypeDescription.UserDefined.Struct(
                containingContract = contract,
                structName = baseName,
                astId = 0,
                canonicalId = s,
                structMembers = components.map {
                    StructTypeMemberType(
                        name = it.name,
                        type = it.toTypeDescription()
                    )
                }
            )
        } else {
            return SolidityTypeDescription.builtin(s) ?: throw IllegalArgumentException("Unknown Solidity type in $this with string rep $s")
        }
    }

    private fun toTypeDescription() : SolidityTypeDescription {
        return parseInternalName(this.internalType ?: this.type)
    }

    fun toSolidityType(): SolidityTypeInstance {
        val typeDescription = this.toTypeDescription()
        return SolidityTypeInstance(typeDescription, null)
    }
}
