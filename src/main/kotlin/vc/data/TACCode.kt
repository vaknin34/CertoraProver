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

@file:kotlinx.serialization.UseSerializers(utils.BigIntegerSerializer::class)
package vc.data

import analysis.numeric.MAX_UINT
import com.certora.collect.*
import tac.Tag
import utils.AmbiSerializable
import utils.KSerializable
import vc.data.ScalarizationSort.*
import java.math.BigInteger

/**
 * Whenever we unpack an unbounded datastructure to scalars, we will use some instance of [ScalarizationSort].
 * It can be either a full [Split] variable (256 bits), a [Packed] variable (with start offset), and
 * [UnscalarizedBuffer] (no scalarization).
 *
 */
@KSerializable
@Treapable
sealed class ScalarizationSort : AmbiSerializable {
    @KSerializable
    data class Split(@KSerializable (with=utils.BigIntegerSerializer::class) val idx: BigInteger) : ScalarizationSort()
    @KSerializable
    data class Packed(val packedStart: ScalarizationSort, val start: Int) : ScalarizationSort()

    // Raw storage array/map
    @KSerializable
    object UnscalarizedBuffer : ScalarizationSort() {
        override fun hashCode() = utils.hashObject(this)
        override fun equals(other: Any?): Boolean = other is UnscalarizedBuffer
        override fun toString(): String = "ScalarizationSort.UnscalarizedBuffer"
        fun readResolve(): Any {
            return ScalarizationSort.UnscalarizedBuffer
        }
    }
}

fun BigInteger.asTACSymbol(): TACSymbol.Const =
    if (this in BigInteger.ZERO..MAX_UINT ) {
        TACSymbol.Const(this, Tag.Bit256)
    } else {
        TACSymbol.Const(this, Tag.Int)
    }
fun BigInteger.asTACSymbol(tag: Tag): TACSymbol.Const = TACSymbol.Const(this, tag)
fun BigInteger.asTACExpr() = this.asTACSymbol().asSym()
fun BigInteger.asTACExpr(tag: Tag) = this.asTACSymbol(tag).asSym()
fun Int.asTACExpr(tag: Tag) = this.toBigInteger().asTACExpr(tag)
fun Long.asTACSymbol(): TACSymbol.Const = this.toBigInteger().asTACSymbol()
fun Long.asTACSymbol(tag: Tag): TACSymbol.Const = TACSymbol.Const(this.toBigInteger(), tag)
fun Int.asTACSymbol(): TACSymbol.Const = this.toBigInteger().asTACSymbol()
fun Int.asTACSymbol(tag: Tag): TACSymbol.Const = TACSymbol.Const(this.toBigInteger(), tag)
fun BigInteger.asBoolTACSymbol(): TACSymbol.Const = TACSymbol.Const(this, Tag.Bool)
fun Boolean.asTACSymbol(): TACSymbol.Const = TACSymbol.Const(this)
fun BigInteger.asIntTACSymbol(): TACSymbol.Const = TACSymbol.Const(this, Tag.Int)
fun Int.asIntTACSymbol(): TACSymbol.Const = TACSymbol.Const(this.toBigInteger(), Tag.Int)

val BigInteger.asTACExpr get() = asTACSymbol().asSym()
val Long.asTACExpr get() = asTACSymbol().asSym()
val Int.asTACExpr get() = asTACSymbol().asSym()
val BigInteger.asBoolTACExpr get() = asBoolTACSymbol().asSym()
val Boolean.asTACExpr get() = asTACSymbol().asSym()
val BigInteger.asIntTACExpr get() = asIntTACSymbol().asSym()
val Int.asIntTACExpr get() = asIntTACSymbol().asSym()
