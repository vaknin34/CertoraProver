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

package scene

import bridge.SourceLanguage
import com.certora.collect.*
import datastructures.stdcollections.*
import spec.CVLReservedVariables
import utils.*

const val CONSTRUCTOR = "constructor"
const val VYPER_CONSTRUCTOR = "__init__"
const val WHOLE_CONTRACT = "wholecontract"

@KSerializable
@Treapable
sealed class MethodAttribute : AmbiSerializable {

    override fun hashCode() = hashObject(this)

    @KSerializable
    object Common : MethodAttribute() {
        fun readResolve(): Any = Common
        override fun hashCode() = hashObject(this)
        override fun toString(): String {
            return "COMMON"
        }
    }
    @KSerializable
    sealed class Unique : MethodAttribute() {
        abstract val methodId: String

        /** The fallback method that a contract will invoke when the name of the called method doesn't match any of the
         * contract's methods */
        @KSerializable
        object Fallback : Unique() {
            fun readResolve(): Any = Fallback
            override fun hashCode() = hashObject(this)
            override val methodId: String = CVLReservedVariables.certorafallback_0.name

            override fun toString(): String {
                return "FALLBACK"
            }
        }
        /** contract's code pre-splitting to methods (the code that includes the dispatcher code) */
        @KSerializable
        object Whole : Unique() {
            fun readResolve(): Any = Whole
            override fun hashCode() = hashObject(this)
            override val methodId: String = WHOLE_CONTRACT

            override fun toString(): String {
                return "WHOLE"
            }
        }
        /** contract's constructor, taken from constructor bytecode */
        @KSerializable
        object Constructor : Unique() {
            fun readResolve(): Any = Constructor
            override fun hashCode() = hashObject(this)
            @Deprecated("should be unsafe to compare to this. use `getIdentifier()` instead")
            override val methodId: String = CONSTRUCTOR

            fun getIdentifier(language: SourceLanguage) =
                when (language) {
                    SourceLanguage.Solidity -> CONSTRUCTOR
                    SourceLanguage.Vyper -> VYPER_CONSTRUCTOR
                    SourceLanguage.Yul -> CONSTRUCTOR // xxx hopefully
                    SourceLanguage.Unknown -> CONSTRUCTOR
                }

            override fun toString(): String {
                return "CONSTRUCTOR"
            }
        }

        companion object {
            fun isUnique(name: String): Boolean {
                listOf(Fallback, Whole, Constructor).forEach {
                    if (it.methodId == name) return true
                }
                return false
            }

        }
    }

}
