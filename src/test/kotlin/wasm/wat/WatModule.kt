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

@DslMarker
annotation class WatDsl

@WatDsl
class WatModuleBuilder {
    val name: String = "\$testmodule"
    private val imports = mutableSetOf<WatImport<*>>()
    private val fields = mutableListOf<String>()

    private var genericFreshName = 0
    internal fun genericFreshName() = "_${genericFreshName++}"

    private var freshLocalParamName = 0
    internal fun freshLocalParamName() = "_${freshLocalParamName++}"

    fun <T : WatResult> import(import: WatImport<T>) = import.also { imports.add(it) }

    fun memory(name: String = genericFreshName(), initialPages: Int = 65536) { fields.add("(memory \$m$name $initialPages)") }

    fun <T : WatType> param(type: T, name: String = freshLocalParamName()) = WatLocal(type, name)

    fun dataSegment(name: String, address: Int, text: String) = dataSegment(name, address, text.toByteArray())

    fun dataSegment(name: String, address: Int, bytes: ByteArray) {
        fun encodeByte(b: Byte) = "\\" + b.toString(16).padStart(2, '0')
        val encoded = bytes.joinToString("") { encodeByte(it) }
        fields.add("(data \$$name (i32.const $address) \"$encoded\")")
    }

    fun <T : WatType> global(name: String, type: T, init: WatExpr<T>): WatGlobal<T> {
        fields.add("(global \$$name $type (${init.op}))")
        return WatGlobal(type, name)
    }

    fun <T : WatResult, TParams> WatInternalFunc<T, TParams>.implement(build: WatFuncBuilder.(TParams) -> Unit): WatInternalFunc<T, TParams> {
        val builder = WatFuncBuilder(this@WatModuleBuilder, this)
        builder.build(typedParams)
        fields.add(builder.toString())
        return this
    }

    override fun toString() = """
        (module $name
            ${imports.joinToString("\n") { it.import }}
            ${fields.joinToString("\n")}
        )
    """
}

/** Create module with no defaults */
fun watModule(
    build: WatModuleBuilder.() -> Unit
) = WatModuleBuilder().also { it.build() }.toString()


/** Create a module with default memory and a single function with no params or result */
fun watFunc(
    exportName: String,
    build: WatFuncBuilder.() -> Unit
) = watModule {
    memory("default_memory", 65536)
    func(exportName = exportName).implement { build() }
}

fun <T1 : WatType> watFunc(
    exportName: String,
    p1: T1,
    build: WatFuncBuilder.(WatLocal<T1>) -> Unit
) = watModule {
    memory("default_memory", 65536)
    func(param(p1), exportName = exportName).implement { (a) -> build(a) }
}

fun <T1 : WatType, T2 : WatType> watFunc(
    exportName: String,
    p1: T1,
    p2: T2,
    build: WatFuncBuilder.(WatLocal<T1>, WatLocal<T2>) -> Unit
) = watModule {
    memory("default_memory", 65536)
    func(param(p1), param(p2), exportName = exportName).implement { (a, b) -> build(a, b) }
}

fun <T1 : WatType, T2 : WatType, T3 : WatType> watFunc(
    exportName: String,
    p1: T1,
    p2: T2,
    p3: T3,
    build: WatFuncBuilder.(WatLocal<T1>, WatLocal<T2>, WatLocal<T3>) -> Unit
) = watModule {
    memory("default_memory", 65536)
    func(param(p1), param(p2), param(p3), exportName = exportName).implement { (a, b, c) -> build(a, b, c) }
}

fun <T1 : WatType, R : WatType> watFunc(
    exportName: String,
    p1: T1,
    r: R,
    build: WatFuncBuilder.(WatLocal<T1>) -> Unit
) = watModule {
    memory("default_memory", 65536)
    func(param(p1), r, exportName = exportName).implement { (a) -> build(a) }
}

fun <T1 : WatType, T2 : WatType, R : WatType> watFunc(
    exportName: String,
    p1: T1,
    p2: T2,
    r: R,
    build: WatFuncBuilder.(WatLocal<T1>, WatLocal<T2>) -> Unit
) = watModule {
    memory("default_memory", 65536)
    func(param(p1), param(p2), r, exportName = exportName).implement { (a, b) -> build(a, b) }
}

fun <T1 : WatType, T2 : WatType, T3 : WatType, R : WatType> watFunc(
    exportName: String,
    p1: T1,
    p2: T2,
    p3: T3,
    r: R,
    build: WatFuncBuilder.(WatLocal<T1>, WatLocal<T2>, WatLocal<T3>) -> Unit
) = watModule {
    memory("default_memory", 65536)
    func(param(p1), param(p2), param(p3), r, exportName = exportName).implement { (a, b, c) -> build(a, b, c) }
}
