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

import compiler.JumpType.Companion.toJumpType
import kotlinx.serialization.Serializable

/**
 * The jump types exposed by Solidity's source maps.
 * https://docs.soliditylang.org/en/v0.6.7/internals/source_mappings.html
 */
@Serializable
enum class JumpType {
    UNKNOWN,
    ENTER,
    EXIT,
    REGULAR
    ;

    companion object {
        fun String.toJumpType(): JumpType =
            when (this) {
                "i" -> ENTER
                "o" -> EXIT
                "-" -> REGULAR
                else -> UNKNOWN
            }

    }
}

@Serializable
data class SrcMapping(val source : Int, val begin : Int, val len : Int, val jumpType: JumpType?) {
    companion object {
        fun fromString(s : String) : SrcMapping {
            val split = s.split(":")
            if (split.size != 3 || split.count { it.toIntOrNull() != null } != 3) {
                throw Exception("Bad source mapping string $s")
            }
            return SrcMapping(
                    split[2].toInt(),
                    split[0].toInt(),
                    split[1].toInt(),
                    split.getOrNull(3)?.toJumpType()
            )
        }
    }
}

typealias VariableMapping = Map<String, Int>

/*
@Serializable
data class SolidityData(val functions : Map<ContractIdentifier,List<SolidityFunction>>,
                        val srcMap : Map<ContractIdentifier, List<SrcMapping>>,
                        val srcList : Map<Int,ContractIdentifier>,
                        val srcToFile : Map<Int,String>,
                        val primaryContrct : ContractIdentifier
)
*/
