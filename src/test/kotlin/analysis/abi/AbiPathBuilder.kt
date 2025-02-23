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

package analysis.abi

import analysis.pta.abi.DecoderAnalysis
import analysis.pta.abi.ObjectPath
import analysis.pta.abi.ObjectPathAnalysis
import analysis.pta.abi.ObjectPathGen
import java.math.BigInteger

interface AbiPathBuilder {
    object Elem
    object Static

    val static get() = Static
    val elem get() = Elem

    fun BigInteger.toRootOffset() = DecoderAnalysis.BufferAccessPath.Offset(this, DecoderAnalysis.BufferAccessPath.Root)
    fun BigInteger.toBuilder() = BufferAccessPathBuilder(this.toRootOffset())
    fun Int.toRootOffset() = this.toBigInteger().toRootOffset()
    fun Int.toBuilder() = this.toBigInteger().toBuilder()
    fun ObjectPath.extend() = ObjectPathBuilder(this)
    class BufferAccessPathBuilder(val path: DecoderAnalysis.BufferAccessPath) {
        constructor(c: BigInteger) : this(DecoderAnalysis.BufferAccessPath.Offset(offset = c, base = DecoderAnalysis.BufferAccessPath.Root))

        operator fun get(@Suppress("UNUSED_PARAMETER") x: Elem) : BufferAccessPathBuilder = BufferAccessPathBuilder(DecoderAnalysis.BufferAccessPath.ArrayElemOf(path, setOf()))

        fun loop(c: BigInteger) = BufferAccessPathBuilder(DecoderAnalysis.BufferAccessPath.StaticStride(strideBy = c, parent = path))
        fun at(c: BigInteger) = BufferAccessPathBuilder(DecoderAnalysis.BufferAccessPath.Offset(offset = c, base = path))

        fun loop(c: Int) = this.loop(c.toBigInteger())
        fun at(c: Int) = this.at(c.toBigInteger())

        val deref: BufferAccessPathBuilder get() = BufferAccessPathBuilder(DecoderAnalysis.BufferAccessPath.Deref(parent = path))

    }

    class ObjectPathBuilder(val path: ObjectPath) {
        operator fun get(@Suppress("UNUSED_PARAMETER") x: Elem) : ObjectPathBuilder = ObjectPathBuilder(ObjectPathGen.ArrayElem(path))
        fun at(c: BigInteger) = ObjectPathBuilder(ObjectPathGen.Field(offset = c, parent = path))
        fun at(c: Int) = this.at(c.toBigInteger())
        operator fun get(@Suppress("UNUSED_PARAMETER") x: Static) = ObjectPathBuilder(ObjectPathGen.StaticArrayField(path))
        val length get() = ObjectPathGen.ArrayLength(path)
    }
}
