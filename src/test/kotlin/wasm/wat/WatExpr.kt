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

package wasm.wat

open class WatExpr<T : WatResult>(val type: T, val op: String? = null, val args: List<WatExpr<*>> = listOf()) {
    constructor(type: T, op: String?, vararg args: WatExpr<*>) : this(type, op, args.toList())

    context(WatBodyBuilder)
    fun build() {
        args.forEach { +it }
        if (op != null) { +op }
    }
}

private val <T : WatType> WatExpr<T>.signSuffix get() = type.signSuffix


// Numeric instructions: https://developer.mozilla.org/en-US/docs/WebAssembly/Reference/Numeric

operator fun i32.invoke(value: Int) = WatExpr(i32, "$this.const $value")
operator fun u32.invoke(value: UInt) = WatExpr(u32, "$this.const $value")
operator fun i64.invoke(value: Long) = WatExpr(i64, "$this.const $value")
operator fun u64.invoke(value: ULong) = WatExpr(u64, "$this.const $value")
operator fun f32.invoke(value: Float) = WatExpr(f32, "$this.const $value")
operator fun f64.invoke(value: Double) = WatExpr(f64, "$this.const $value")

operator fun i32.invoke(value: Boolean) = i32(if (value) { 1 } else { 0 })

infix fun <T : WatType> WatExpr<T>.eq(that: WatExpr<T>) = WatExpr(i32, "$type.eq", this, that)
infix fun <T : WatType> WatExpr<T>.ne(that: WatExpr<T>) = WatExpr(i32, "$type.ne", this, that)

fun <T : WatType.Int> WatExpr<T>.eqz() = WatExpr(i32, "$type.eqz", this)

fun not(v: WatExpr<i32>) = v.eqz()

infix fun <T : WatType> WatExpr<T>.gt(that: WatExpr<T>) = WatExpr(i32, "$type.gt$signSuffix", this, that)
infix fun <T : WatType> WatExpr<T>.lt(that: WatExpr<T>) = WatExpr(i32, "$type.lt$signSuffix", this, that)
infix fun <T : WatType> WatExpr<T>.ge(that: WatExpr<T>) = WatExpr(i32, "$type.ge$signSuffix", this, that)
infix fun <T : WatType> WatExpr<T>.le(that: WatExpr<T>) = WatExpr(i32, "$type.le$signSuffix", this, that)

infix operator fun <T : WatType> WatExpr<T>.plus(that: WatExpr<T>) = WatExpr(type, "$type.add", this, that)
infix operator fun <T : WatType> WatExpr<T>.minus(that: WatExpr<T>) = WatExpr(type, "$type.sub", this, that)
infix operator fun <T : WatType> WatExpr<T>.times(that: WatExpr<T>) = WatExpr(type, "$type.mul", this, that)
infix operator fun <T : WatType> WatExpr<T>.div(that: WatExpr<T>) = WatExpr(type, "$type.div$signSuffix", this, that)
infix operator fun <T : WatType.Int> WatExpr<T>.rem(that: WatExpr<T>) = WatExpr(type, "$type.rem$signSuffix", this, that)

@JvmName("i32_to_i32") fun <T1 : WatType.Int32, T2 : WatType.Int32> WatExpr<T1>.to(thatType: T2) = WatExpr(thatType, null, this)
@JvmName("i64_to_i64") fun <T1 : WatType.Int64, T2 : WatType.Int64> WatExpr<T1>.to(thatType: T2) = WatExpr(thatType, null, this)
@JvmName("i32_to_i64") fun <T1 : WatType.Int32, T2 : WatType.Int64> WatExpr<T1>.to(thatType: T2) = WatExpr(thatType, "$thatType.extend_$type$signSuffix", this)
@JvmName("i64_to_i32") fun <T1 : WatType.Int64, T2 : WatType.Int32> WatExpr<T1>.to(thatType: T2) = WatExpr(thatType, "$thatType.wrap_$type", this)
@JvmName("f32_to_f64") fun WatExpr<f32>.to(thatType: f64) = WatExpr(thatType, "$thatType.promote_$type", this)
@JvmName("f64_to_f32") fun WatExpr<f64>.to(thatType: f32) = WatExpr(thatType, "$thatType.demote_$type", this)
@JvmName("i_to_f") fun <T1 : WatType.Int, T2: WatType.Float> WatExpr<T1>.to(thatType: T2) = WatExpr(thatType, "$thatType.convert_$type$signSuffix", this)
@JvmName("f_to_i") fun <T1 : WatType.Float, T2: WatType.Int> WatExpr<T1>.to(thatType: T2) = WatExpr(thatType, "$thatType.trunc_$type$signSuffix", this)

fun <T : WatType.Int32> WatExpr<T>.reinterpretAs(thatType: f32) = WatExpr(thatType, "$thatType.reinterpret_$type", this)
fun <T : WatType.Int64> WatExpr<T>.reinterpretAs(thatType: f64) = WatExpr(thatType, "$thatType.reinterpret_$type", this)
fun <T : WatType.Int32> WatExpr<f32>.reinterpretAs(thatType: T) = WatExpr(thatType, "$thatType.reinterpret_$type", this)
fun <T : WatType.Int64> WatExpr<f64>.reinterpretAs(thatType: T) = WatExpr(thatType, "$thatType.reinterpret_$type", this)

fun <T : WatType.Float> min(a: WatExpr<T>, b: WatExpr<T>) = WatExpr(a.type, "${a.type}.min", a, b)
fun <T : WatType.Float> max(a: WatExpr<T>, b: WatExpr<T>) = WatExpr(a.type, "${a.type}.min", a, b)

fun <T : WatType.Float> WatExpr<T>.nearest() = WatExpr(type, "$type.nearest", this)
fun <T : WatType.Float> WatExpr<T>.ceil() = WatExpr(type, "$type.ceil", this)
fun <T : WatType.Float> WatExpr<T>.floor() = WatExpr(type, "$type.floor", this)
fun <T : WatType.Float> WatExpr<T>.trunc() = WatExpr(type, "$type.trunc", this)
fun <T : WatType.Float> WatExpr<T>.abs() = WatExpr(type, "$type.abs", this)
operator fun <T : WatType.Float> WatExpr<T>.unaryMinus() = WatExpr(type, "$type.neg", this)
fun <T : WatType.Float> WatExpr<T>.sqrt() = WatExpr(type, "$type.sqrt", this)
fun <T : WatType.Float> WatExpr<T>.copySign(that: WatExpr<T>) = WatExpr(type, "$type.copysign", this, that)

infix fun <T : WatType.Int> WatExpr<T>.and(that: WatExpr<T>) = WatExpr(type, "$type.and", this, that)
infix fun <T : WatType.Int> WatExpr<T>.or(that: WatExpr<T>) = WatExpr(type, "$type.or", this, that)
infix fun <T : WatType.Int> WatExpr<T>.xor(that: WatExpr<T>) = WatExpr(type, "$type.xor", this, that)

infix fun <T : WatType.Int> WatExpr<T>.shl(that: WatExpr<T>) = WatExpr(type, "$type.shl", this, that)
infix fun <T : WatType.Int> WatExpr<T>.shr(that: WatExpr<T>) = WatExpr(type, "$type.shr$signSuffix", this, that)

infix fun <T : WatType.Int> WatExpr<T>.rotl(that: WatExpr<T>) = WatExpr(type, "$type.rotl", this, that)
infix fun <T : WatType.Int> WatExpr<T>.rotr(that: WatExpr<T>) = WatExpr(type, "$type.rotr", this, that)

fun <T : WatType.Int> WatExpr<T>.clz() = WatExpr(type, "$type.clz", this)
fun <T : WatType.Int> WatExpr<T>.ctz() = WatExpr(type, "$type.ctz", this)
fun <T : WatType.Int> WatExpr<T>.popcnt() = WatExpr(type, "$type.popcnt", this)
