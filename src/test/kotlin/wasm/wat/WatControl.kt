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
class WatNamedBlockBuilder(
    override val moduleBuilder: WatModuleBuilder,
    override val funcBuilder: WatFuncBuilder,
    val name: String,
    private val blockType: String
) : WatBodyBuilder() {
    override fun toString() = """
        $blockType $name
            ${super.toString()}
        end
    """
}

context(WatBodyBuilder)
fun block(name: String = moduleBuilder.genericFreshName(), build: WatNamedBlockBuilder.() -> Unit) {
    +WatNamedBlockBuilder(moduleBuilder, funcBuilder, "\$$name", "block").also { it.build() }.toString()
}

context(WatBodyBuilder)
fun loop(name: String = moduleBuilder.genericFreshName(), build: WatNamedBlockBuilder.() -> Unit) {
    +WatNamedBlockBuilder(moduleBuilder, funcBuilder, "\$$name", "loop").also { it.build() }.toString()
}

context(WatBodyBuilder)
fun branch(to: WatNamedBlockBuilder) {
    +"br ${to.name}"
}

context(WatNamedBlockBuilder)
fun branch() {
    +"br $name"
}

context(WatBodyBuilder)
fun branchIf(cond: WatExpr<i32>, to: WatNamedBlockBuilder) {
    +cond
    +"br_if ${to.name}"
}

context(WatNamedBlockBuilder)
fun branchIf(cond: WatExpr<i32>) {
    +cond
    +"br_if $name"
}

context(WatBodyBuilder)
operator fun <T : WatType> WatFunc<T>.invoke(vararg args: WatExpr<*>): WatExpr<T> {
    forceImport()
    return immediate(WatExpr(result, "call $this", *args))
}

context(WatBodyBuilder)
operator fun WatFunc<WatResult.None>.invoke(vararg args: WatExpr<*>) {
    forceImport()
    +WatExpr(result, "call $this", *args)
}

context(WatBodyBuilder)
fun ite(cond: WatExpr<i32>, then: WatBodyBuilder.() -> Unit, orElse: (WatBodyBuilder.() -> Unit)?) {
    +cond
    +"if"
    this@WatBodyBuilder.then()
    if (orElse != null) {
        +"else"
        this@WatBodyBuilder.orElse()
    }
    +"end"
}

context(WatBodyBuilder)
fun ite(cond: WatExpr<i32>, then: WatBodyBuilder.() -> Unit) = ite(cond, then, null)

context(WatBodyBuilder)
fun returnResult(value: WatExpr<*>) {
    +value
    +"return"
}

context(WatBodyBuilder)
fun returnNoResult() {
    +"return"
}

context(WatBodyBuilder)
fun select(cond: WatExpr<i32>, then: WatExpr<*>, orElse: WatExpr<*>) {
    +then
    +orElse
    +cond
    +"select"
}
