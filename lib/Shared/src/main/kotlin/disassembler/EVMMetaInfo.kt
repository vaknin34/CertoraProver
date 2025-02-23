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

package disassembler

import com.certora.collect.*
import compiler.JumpType
import compiler.VariableMapping
import utils.*
import java.io.Serializable

@Treapable
data class EVMMetaInfo(
    val source : Int,
    val begin : Int,
    val end : Int,
    val varmap : VariableMapping?,
    val opcode: UByte,
    val jumpType: JumpType?
): Serializable {
    override fun hashCode() = hash { it + source + begin + end + varmap + opcode + jumpType }
}
