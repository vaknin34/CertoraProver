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

@WatDsl
abstract class WatBodyBuilder() {
    abstract val moduleBuilder: WatModuleBuilder
    abstract val funcBuilder: WatFuncBuilder

    private val body = mutableListOf<String>()

    override fun toString() = body.joinToString("\n")

    /**
        "Inline assembly" support: Allow any wasm text to be added like so:
        ```
            +"i32.const 42"
        ```
     */
    operator fun String.unaryPlus() {
        body.add(this)
    }

    /**
        Insert an expression evaluation (leaving the result on the WASM stack).
        ```
            +(a + b)
            +"return"
        ```
     */
    operator fun WatExpr<*>.unaryPlus() {
        build()
    }

    /**
        Force an expression to be immediately evaluated, store the result in a local, and return it as an expression.
     */
    fun <T : WatType> immediate(value: WatExpr<T>): WatExpr<T> =
        funcBuilder.local(value.type).also { it.set(value) }
}
