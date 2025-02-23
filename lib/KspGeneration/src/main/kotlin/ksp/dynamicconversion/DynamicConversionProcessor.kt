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

package ksp.dynamicconversion

import com.google.devtools.ksp.processing.*
import com.google.devtools.ksp.symbol.*

/**
 * Ksp processor that provides dynamic conversion extension functions `copy()`
 * and `constructFrom()` that both take [Map<String,Any>] to override and
 * initialize, respectively, individual properties instead of using named
 * arguments. For a data class `T` annotated with [AddDynamicConversion],
 * it adds `fun T.copy(overrides: Map<String, Any>?): T` and
 * `fun T.Companion.constructFrom(params: Map<String, Any>): T`. The map values
 * are given as [Any] and converted to the appropriate type of the respective
 * property using generic conversion ([convert]) or custom converters
 * (via [ConvertibleWith]). For `constructFrom()` the map needs to contain
 * values for all properties that do not have default values in the declaration
 * of the primary constructor of `T`. All remaining properties are then updated
 *
 */
class DynamicConversionProcessor(
    val logger: KSPLogger,
    private val codeGen: CodeGenerator,
): SymbolProcessor {

    /**
     * Figure out how to convert an arbitrary value to the type of the given
     * parameter [param]. Returns a lambda that takes a string (the variable
     * name that holds the value) and returns the conversion expression as a
     * string.
     * The resulting expression is always a call to [convert] or [convertList],
     * possibly with a custom converter if [param] is annotated with
     * [ConvertibleWith].
     */
    private fun getConversionInfo(param: KSValueParameter): (String) -> String {
        val isList = (param.type.resolve().declaration.simpleName.asString() == "List")
        val convType = param.annotations.firstOrNull { a ->
            a.shortName.getShortName() == ConvertibleWith::class.simpleName!! &&
                    a.annotationType.resolve().declaration.qualifiedName?.asString() == ConvertibleWith::class.qualifiedName
        }?.arguments?.first()?.value as KSType?
        return if (convType == null) {
            if (isList) {
                { "convertList(${it})" }
            } else {
                { "convert(${it})" }
            }
        } else {
            if (isList) {
                { "convertList(${it}, ${convType.declaration.qualifiedName!!.asString()}())" }
            } else {
                { "convert(${it}, ${convType.declaration.qualifiedName!!.asString()}())" }
            }
        }
    }

    /**
     * Add the dynamic conversion routines for the given data class.
     */
    private fun addDynamicConversion(ksa: KSClassDeclaration) {
        val fullClassName = ksa.qualifiedName!!.asString()
        val out = codeGen.createNewFile(
            Dependencies(false, ksa.containingFile!!),
            ksa.packageName.asString(),
            "${fullClassName}_dynamicConversion",
            "kt"
        )

        val writer = out.bufferedWriter()
        writer.write("""
package ${ksa.packageName.asString()}

import ksp.dynamicconversion.*

/**
*   Generated by [${this::class.qualifiedName}]
*/
fun ${fullClassName}.copy(overrides: Map<String, Any>?): ${fullClassName} {
    if (overrides == null || overrides.isEmpty()) return this
    var res = this
    overrides.forEach { (k,v) ->
        res = when (k) {
""".trimIndent())
        ksa.primaryConstructor!!.parameters.forEach { param ->
            val pname = param.name!!.asString()
            writer.write("""
            "${pname}" -> res.copy(${pname} = ${getConversionInfo(param)("v")})""")
        }
        writer.write("""
            else -> throw DynamicConversionException("Unknown property \"${'$'}{k}\" for ${fullClassName}")
        }
    }
    return res
}

fun ${fullClassName}.Companion.constructFrom(params: Map<String, Any>): ${fullClassName} {
    val p = params.toMutableMap()
    return ${fullClassName}(""")
        ksa.primaryConstructor!!.parameters.filterNot { it.hasDefault }.forEach {
            val n = it.name!!.asString()
            writer.write("""
        ${n} = p.remove("${n}")?.let { ${getConversionInfo(it)("it")} }
            ?: throw DynamicConversionException("Mandatory constructor argument \"${n}\" for ${fullClassName} is missing"),""")
        }
        writer.write("""
    ).copy(p)
}
""")
        writer.flush()
        out.close()
    }

    /**
     * Main process method. Calls out to [addDynamicConversion] for all data
     * classes annotated with [AddDynamicConversion].
     */
    override fun process(resolver: Resolver): List<KSAnnotated> {
        resolver.getSymbolsWithAnnotation(AddDynamicConversion::class.java.canonicalName).mapNotNull {
            it as? KSClassDeclaration
        }.filter {
            it.classKind == ClassKind.CLASS && Modifier.DATA in it.modifiers
        }.forEach {
            addDynamicConversion(it)
        }
        return listOf()
    }
}
