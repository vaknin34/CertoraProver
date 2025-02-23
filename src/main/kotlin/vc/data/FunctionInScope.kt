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

package vc.data

import com.certora.collect.*
import spec.cvlast.CVLType
import tac.Tag
import utils.HasKSerializable
import utils.KSerializable
import utils.hash
import utils.runIf
import java.io.Serializable

@KSerializable
sealed class FunctionInScope : Serializable, HasKSerializable {

    abstract val name: String
    abstract val paramSorts: List<Tag>
    abstract val returnSort: Tag
    abstract val attribute: UFAttribute
    abstract val decl: String

    override fun toString(): String = decl

    /**
     * Note: this might as well be called "GhostMap" or so for all current intents and purposes.
     *  If we use "uninterpreted functions" for something else some day, we might introduce a further subdivision then.
     */
    @KSerializable
    @Treapable
    data class UF(
        override val name: String,
        override val paramSorts: List<Tag>,
        override val returnSort: Tag,
        override val attribute: UFAttribute = UFAttribute.None,
        val cvlResultType: CVLType.PureCVLType,
        val cvlParamTypes: List<CVLType.PureCVLType>,
        val declarationName: String,
        val persistent: Boolean = false,
    ) : FunctionInScope() {
        override val decl = "UninterpFunc $name(${paramSorts.joinToString(", ")}) returns $returnSort ufAttribute=$attribute"

        override fun hashCode(): Int = hash { it + name + paramSorts + returnSort + attribute + decl + cvlResultType +
                                                 cvlParamTypes + persistent }
        val asTag: Tag
            get() = if (this.paramSorts.isEmpty()) {
                this.returnSort
            } else {
                Tag.GhostMap(paramSorts, returnSort)
            }

        fun asVarOrNull() =
            runIf(paramSorts.isEmpty()) { TACSymbol.Var(name, returnSort) }
    }

    @KSerializable
    @Treapable
    data class Builtin(val tacBif: TACBuiltInFunction) : FunctionInScope() {

        override val name: String
            get() = tacBif.name
        override val paramSorts: List<Tag>
            get() = tacBif.paramSorts
        override val returnSort: Tag
            get() = tacBif.returnSort
        override val attribute: UFAttribute
            get() = tacBif.ufAttribute

        override val decl = "import BuiltinFunc $name(${paramSorts.joinToString(", ")}) returns $returnSort ufAttribute=$attribute"

    }
}
