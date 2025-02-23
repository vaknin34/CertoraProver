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

package builders

import java.math.BigInteger

sealed class Type: Typed {
    abstract val static: Boolean
    abstract val sizeInBytes: BigInteger

    sealed class Primitive: Type() {
        override val static
            get() = true

        abstract val name: String

        data class Integer(val signed: Boolean, val bytes: BigInteger): Primitive() {
            override val sizeInBytes: BigInteger
                get() = bytes
            override val type: Type
                get() = Integer(signed, bytes)

            override val name: String
                get() {
                    val u = if (signed) {
                        ""
                    } else {
                        "u"
                    }
                    return "${u}int${bytes * 8.toBigInteger()}"
                }
        }

        data object Bytes32: Primitive() {
            override val sizeInBytes: BigInteger
                get() = 32.toBigInteger()
            override val type: Type
                get() = Bytes32
            override val name: String
                get() = "bytes32"
        }

        data object Address: Primitive() {
            override val name: String
                get() = "address"
            override val sizeInBytes: BigInteger
                get() = 24.toBigInteger()
            override val type: Type
                get() = Address
        }

    }

    data class Array(val elements: Type): Type() {
        override val sizeInBytes: BigInteger
            get() = 32.toBigInteger()
        override val type: Type
            get() = this.copy()
        override val static: Boolean
            get() = false
    }

    data class StaticArray(val elements: Type, val len: BigInteger) : Type() {
        override val static: Boolean
            get() = true
        override val sizeInBytes: BigInteger
            get() = elements.sizeInBytes * len
        override val type: Type
            get() = this

    }

    data class Struct(val members: Map<BigInteger, Type>): Type() {
        override val sizeInBytes: BigInteger
            get() =
                if (static) {
                    members.values.fold(BigInteger.ZERO) { a, b ->
                        a + b.sizeInBytes
                    }
                } else {
                    32.toBigInteger()
                }
        override val type: Type
            get() = this.copy()
        override val static: Boolean
            get() = members.values.all { it.static }
    }
}
