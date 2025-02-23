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

interface WatFunc<T : WatResult> {
    val result: T

    context(WatBodyBuilder)
    fun forceImport()
}

data class WatImport<T : WatResult>(
    val module: String,
    val func: String,
    val params: List<WatType> = listOf(),
    override val result: T,
    val name: String = "$module.$func"
) : WatFunc<T> {
    val paramsString get() = params.takeIf { it.isNotEmpty() }?.joinToString(" ", "(param ", ")").orEmpty()

    val resultsString get() = (result as? WatType)?.let { "(result $it)" }.orEmpty()

    val import = "(func $this (import \"$module\" \"$func\") $paramsString $resultsString)"

    context(WatBodyBuilder)
    override fun forceImport() { this@WatBodyBuilder.moduleBuilder.import(this) }

    override fun toString() = "\$$name"

    companion object {
        operator fun invoke(module: String, func: String, params: List<WatType>) =
            WatImport(module, func, params, WatResult.None)
    }
}

class WatInternalFunc<T : WatResult, TParams>(
    val name: String,
    val exportName: String?,
    override val result: T,
    val params: List<WatLocal<*>>,
    val typedParams: TParams
) : WatFunc<T> {
    context(WatBodyBuilder)
    override fun forceImport() {
        // nothing to import
    }
    override fun toString() = "\$f$name"
}

@WatDsl
class WatFuncBuilder(
    override val moduleBuilder: WatModuleBuilder,
    val func: WatInternalFunc<*, *>,
) : WatBodyBuilder() {
    override val funcBuilder get() = this

    private val locals = mutableSetOf<String>()
    private val body = mutableListOf<String>()

    fun <T : WatType> local(type: T, name: String = moduleBuilder.freshLocalParamName()) =
        WatLocal(type, name).also {
            locals.add("(local $it $type)")
        }

    fun <T : WatType> local(v: WatExpr<T>, name: String = moduleBuilder.freshLocalParamName()) =
        local(v.type, name).also {
            it.set(v)
        }

    private val export get() = func.exportName?.let { "(export \"$it\")" }.orEmpty()
    private val params get() = func.params.joinToString("\n") { "(param \$${it.name} ${it.type})" }
    private val result get() = func.result.takeIf { it != WatResult.None }?.let { "(result $it)" }.orEmpty()

    override fun toString() = """
        (func $func $export $params $result ${locals.joinToString(" ")}
            ${super.toString()}
        )
    """
}

// Internal function factories: 0-3 params, no result:
context(WatModuleBuilder)
fun func(name: String = genericFreshName(), exportName: String? = null) =
    WatInternalFunc(name, exportName, WatResult.None, emptyList(), Unit)
context(WatModuleBuilder)
fun <T1 : WatType> func(p1: WatLocal<T1>, name: String = genericFreshName(), exportName: String? = null) =
    WatInternalFunc(name, exportName, WatResult.None, listOf(p1), listOf(p1))
context(WatModuleBuilder)
fun <T1 : WatType, T2 : WatType> func(p1: WatLocal<T1>, p2: WatLocal<T2>, name: String = genericFreshName(), exportName: String? = null) =
    WatInternalFunc(name, exportName, WatResult.None, listOf(p1, p2), Pair(p1, p2))
context(WatModuleBuilder)
fun <T1 : WatType, T2 : WatType, T3 : WatType> func(p1: WatLocal<T1>, p2: WatLocal<T2>, p3: WatLocal<T3>, name: String = genericFreshName(), exportName: String? = null) =
    WatInternalFunc(name, exportName, WatResult.None, listOf(p1, p2, p3), Triple(p1, p2, p3))


// Internal function factories: 0-3 params, with result:
context(WatModuleBuilder)
fun <R : WatType> func(r: R, name: String = genericFreshName(), exportName: String? = null) =
    WatInternalFunc(name, exportName, r, emptyList(), Unit)
context(WatModuleBuilder)
fun <T1 : WatType, R : WatType> func(p1: WatLocal<T1>, r: R, name: String = genericFreshName(), exportName: String? = null) =
    WatInternalFunc(name, exportName, r, listOf(p1), listOf(p1))
context(WatModuleBuilder)
fun <T1 : WatType, T2 : WatType, R : WatType> func(p1: WatLocal<T1>, p2: WatLocal<T2>, r: R, name: String = genericFreshName(), exportName: String? = null) =
    WatInternalFunc(name, exportName, r, listOf(p1, p2), Pair(p1, p2))
context(WatModuleBuilder)
fun <T1 : WatType, T2 : WatType, T3 : WatType, R : WatType> func(p1: WatLocal<T1>, p2: WatLocal<T2>, p3: WatLocal<T3>, r: R, name: String = genericFreshName(), exportName: String? = null) =
    WatInternalFunc(name, exportName, r, listOf(p1, p2, p3), Triple(p1, p2, p3))
