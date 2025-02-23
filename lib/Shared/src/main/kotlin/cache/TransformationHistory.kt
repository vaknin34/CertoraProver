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

package cache

import java.math.BigInteger

private tailrec fun search(h: TransformationHistory, f: String) : Boolean {
    return when(h) {
        is TransformationHistory.InitialLoad -> false
        is TransformationHistory.Clone -> search(h.prev, f)
        is TransformationHistory.Transform -> {
            if(h.id == f) {
                true
            } else {
                search(h.prev, f)
            }
        }
    }
}

data class ContractLoad(val contract: String, val component: Component) {
    sealed class Component {
        /**
          The split, raw code of each method
         */
        object Codes : Component() {
            override fun toString(): String = "CODES"
        }

        /**
           The whole method passes (DSA, etc.)
         */
        object WholeMethod : Component() {
            override fun toString(): String = "WHOLE-METHOD"
        }

        object RuntimeDisassembly : Component() {
            override fun toString(): String = "RUNTIME-DISASSEMBLY"
        }

        object ConstructorDisassembly : Component() {
            override fun toString(): String = "CONSTRUCTOR-DISASSEMBLY"
        }

        /**
           Decompile
         */
        object Decompilation : Component() {
            override fun toString(): String = "DECOMPILATION"
        }
        /**
          Constructor pass
         */
        object Constructor : Component() {
            override fun toString(): String = "CONSTRUCTOR"
        }

        /**
         * Disassemble and initial decompilation
         */
        data class MethodDecompile(val methodName: String, val sighash: BigInteger?) : Component()

        /**
          Load and initial pass on method [methodName]
         */
        data class MethodLoad(val methodName: String, val sighash: BigInteger?) : Component()
    }
}

sealed class TransformationHistory {
    object InitialLoad : TransformationHistory()
    data class Transform(val id: String, val prev: TransformationHistory) : TransformationHistory()

    data class Clone(val address: BigInteger, val prev: TransformationHistory) : TransformationHistory()

    fun contains(f: String): Boolean = search(this, f)
}
