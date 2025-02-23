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

/**
    Represents the result of an expression or function call.  Some functions may not return a value, in which case
    the result is [WatResult.None].  In all other cases, the result is a [WatType].
 */
interface WatResult {
    object None : WatResult
}

/** A result type of i32, i64, f32, or f64 */
sealed class WatType : WatResult {
    abstract val signSuffix: String

    /** The wasm "i32" or "i64" type */
    sealed class Int : WatType()

    /** The wasm "f32" or "f64" type */
    sealed class Float : WatType() { override val signSuffix = "" }

    // The real wasm "i32" and "i64" types.  We derive synthetic signed and unsigned variants of these.
    sealed class Int32 : WatType.Int() { final override fun toString() = "i32" }
    sealed class Int64 : WatType.Int() { final override fun toString() = "i64" }
}

// These are at the top level to avoid needing to import them individually:

object i32 : WatType.Int32() { override val signSuffix = "_s" }
object u32 : WatType.Int32() { override val signSuffix = "_u" }
object i64 : WatType.Int64() { override val signSuffix = "_s" }
object u64 : WatType.Int64() { override val signSuffix = "_u" }
object f32 : WatType.Float() { override fun toString() = "f32" }
object f64 : WatType.Float() { override fun toString() = "f64" }
