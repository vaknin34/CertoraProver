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

context(WatBodyBuilder)
fun growMemory(pages: WatExpr<i32>) = immediate(WatExpr(i32, "memory.grow", pages))

context(WatBodyBuilder)
fun memorySize() = immediate(WatExpr(i32, "memory.size"))

context(WatBodyBuilder)
fun <T : WatType> T.load(offset: WatExpr<i32>) = immediate(WatExpr(this, "$this.load", offset))

context(WatBodyBuilder)
fun <T : WatType.Int64> T.load32(offset: WatExpr<i32>) = immediate(WatExpr(this, "$this.load32$signSuffix", offset))

context(WatBodyBuilder)
fun <T : WatType.Int> T.load16(offset: WatExpr<i32>) = immediate(WatExpr(this, "$this.load16$signSuffix", offset))

context(WatBodyBuilder)
fun <T : WatType.Int> T.load8(offset: WatExpr<i32>) = immediate(WatExpr(this, "$this.load8$signSuffix", offset))

context(WatBodyBuilder)
fun <T : WatType> T.store(offset: WatExpr<i32>, value: WatExpr<T>) {
    +offset
    +value
    +"$this.store"
}

context(WatBodyBuilder)
fun <T : WatType.Int64> T.store32(offset: WatExpr<i32>, value: WatExpr<T>) {
    +offset
    +value
    +"$this.store32"
}

context(WatBodyBuilder)
fun <T : WatType.Int> T.store16(offset: WatExpr<i32>, value: WatExpr<T>) {
    +offset
    +value
    +"$this.store16"
}

context(WatBodyBuilder)
fun <T : WatType.Int> T.store8(offset: WatExpr<i32>, value: WatExpr<T>) {
    +offset
    +value
    +"$this.store8"
}

context(WatBodyBuilder)
fun memoryCopy(to: WatExpr<i32>, from: WatExpr<i32>, size: WatExpr<i32>) {
    +to
    +from
    +size
    +"memory.copy"
}

context(WatBodyBuilder)
fun memoryFill(to: WatExpr<i32>, value: WatExpr<i32>, size: WatExpr<i32>) {
    +to
    +value
    +size
    +"memory.fill"
}
