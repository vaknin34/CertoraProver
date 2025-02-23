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

package wasm.host.soroban

import wasm.*
import wasm.wat.*

private val Val.Tag.shift get() = when(this) {
    Val.Tag.U32Val, Val.Tag.I32Val -> 32
    else -> 8
}

/**
    Push a tagged constant onto the stack
 */
operator fun Val.Tag.invoke(value: Long): WatExpr<i64> {
    check(value shl shift shr shift == value) { "Value $value is too large for a $this" }
    val v = (value shl shift) or this@Tag.value.toLong()
    return WatExpr(i64, "i64.const $v")
}

operator fun Val.Tag.invoke(value: Int) = this(value.toLong())
operator fun Val.Tag.invoke(value: Byte) = this(value.toUByte().toLong())

fun WatExpr<i64>.hasTag(tag: Val.Tag) = this and i64(0xFF) eq i64(tag.value.toLong())

context(WatBodyBuilder)
fun WatExpr<i64>.decode(tag: Val.Tag): WatExpr<i64> {
    certoraAssert(hasTag(tag))
    return when (tag.signed) {
        true -> this shr i64(tag.shift.toLong())
        false -> (this.to(u64) shr u64(tag.shift.toULong())).to(i64)
        else -> error("Cannot decode $tag")
    }
}

context(WatBodyBuilder)
fun WatExpr<i64>.decodeU32Val(): WatExpr<u32> = decode(Val.Tag.U32Val).to(u32)

context(WatBodyBuilder)
fun WatExpr<i64>.decodeI32Val(): WatExpr<i32> = decode(Val.Tag.I32Val).to(i32)

val VoidVal = Val.Tag.Void(0)
val TrueVal = Val.Tag.True(0)
val FalseVal = Val.Tag.False(0)

context(WatBodyBuilder)
infix fun WatExpr<i64>.valEq(other: WatExpr<i64>) = SorobanImport.Context.obj_cmp(this, other) eq i64(0)
