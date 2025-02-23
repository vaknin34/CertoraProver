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

package ksp.classlists

import com.google.devtools.ksp.KspExperimental
import com.google.devtools.ksp.getAnnotationsByType
import com.google.devtools.ksp.processing.*
import com.google.devtools.ksp.symbol.*
import ksp.dependencies
import ksp.getAnnotations

/**
 * Adds an `instances` field to the annotation class's companion.  `instances` is a mapping containing all instances of
 * the annotation class, indexed by their [kotlin.reflect.KClass] objects.  The annotated class must have a `companion
 * object` - since KSP cannot modify an existing class it cannot add the companion object, but it does add extension
 * methods.
 *
 * For example:
 *
 *     @ListClasses annotation class ExampleAnnotation {
 *         companion object
 *     }
 *
 *     @ExampleAnnotation class Foo
 *     @ExampleAnnotation class Bar
 *
 *     val fooAnnotation : ExampleAnnotation = ExampleAnnotation.instances[Foo::class]
 *     val allExamples : List<ExampleAnnotation> = ExampleAnnotation.instances.values
 *
 * This provides a lightweight alternative to reflection.
 *
 * Note: currently the supported annotation fields are strings, enums, and numbers; see [asKotlinExpression].
 */
@Target(AnnotationTarget.ANNOTATION_CLASS)
@Retention(AnnotationRetention.SOURCE)
annotation class ListClasses

/**
 * KSP SymbolProcessor that generates the `instance` fields of the [ListClasses] annotation classes
 */
class ListClassesProcessor(
    private val logger: KSPLogger,
    private val codeGen: CodeGenerator,
) : SymbolProcessor {

    /** Generate the `instance` field for all [ListClasses] annotations */
    override fun process(resolver: Resolver): List<KSAnnotated> {
        resolver.getAnnotations<KSClassDeclaration,ListClasses>().forEach { processAnnotationType(resolver, it.first) }
        return emptyList()
    }

    /** Generate the file for [annotationType] */
    @OptIn(KspExperimental::class)
    private fun processAnnotationType(resolver : Resolver, annotationType: KSClassDeclaration) {
        val companionClassName = resolver.getKSNameFromString(annotationType.qualifiedName!!.asString() + ".Companion")
        if (resolver.getClassDeclarationByName(companionClassName) == null) {
            logger.error(
                "Annotation classes marked with @${ListClasses::class.simpleName} must have companion objects; " +
                "${annotationType.simpleName.asString()} does not", annotationType
            )
        }

        val isRepeatable = annotationType.getAnnotationsByType(Repeatable::class).toList().isNotEmpty()

        val classes = resolver.getAnnotations<KSClassDeclaration>(annotationType)
        codeGen.createNewFile(
            dependencies = dependencies(listOf(annotationType), classes.map { it.first }),
            packageName = annotationType.packageName.asString(),
            fileName = "${annotationType.simpleName.asString()}List",
            extensionName = "kt"
        ).write(fileText(annotationType, classes, isRepeatable).toByteArray())
    }

    /**
     * Return the generated code that adds an `instances` field to [annotationType] containing [classes].
     *
     * For example:
     *
     *       val ExampleAnnotation.Companion.instances : Map<KClass<*>,ExampleAnnotation> = listOf(
     *           package.foo.Foo::class to ExampleAnnotation("foo field", "foo field 2"),
     *           package.bar.Bar::class to ExampleAnnotation("bar field", "bar field 2"),
     *       ).toMap()
     *
     * If [isRepeatable], the instances variable's entries are lists of annotation objects instead of single annotation objects
     *
     * Requires annotations in [classes] are instances of [annotationType]
     */
    private fun fileText(annotationType : KSClassDeclaration, classes : List<Pair<KSClassDeclaration, KSAnnotation>>, isRepeatable : Boolean)
      = """
        package ${annotationType.packageName.asString()}
        import kotlin.reflect.KClass

        /** map from error ID to error type */
        val ${annotationType.simpleName.asString()}.Companion.instances  : Map<KClass<*>,${instanceType(annotationType, isRepeatable)}>
            get() = _instances

        @Suppress("ImportStdCollections")
        private val _instances : Map<KClass<*>,${instanceType(annotationType,isRepeatable)}> = listOf(${classes.joinToString("") { (classDecl,annotation) -> """
            ${classDecl.qualifiedName!!.asString()}::class to ${annotationType.simpleName.asString()}(${annotation.arguments.joinToString("") { property -> """
                ${property.name!!.asString()} = ${property.value.asKotlinExpression()},"""}}
            ),"""}}
        )${buildMap(isRepeatable)}

        """.trimIndent()

    /** @return A string containing the type of the values of the _instances map */
    private fun instanceType(annotationType: KSClassDeclaration, isRepeatable: Boolean) : String
        = if(isRepeatable) { "List<${annotationType.simpleName.asString()}>" } else { annotationType.simpleName.asString() }

    /** @return A string containing the method call to convert a list of pairs into an _instances map */
    private fun buildMap(isRepeatable: Boolean) : String {
        return if (isRepeatable) {
            ".groupBy({ it.first }, { it.second })"
        } else {
            ".toMap()"
        }
    }
}

/**
 * Output a string containing a Kotlin expression that evaluates to `this`.
 *
 * Note: currently only tested for
 *  - null
 *  - [String]
 *  - [Number]
 *  - enum types
 *  - arrays of strings
 */
private fun Any?.asKotlinExpression() : String = when {
    this == null -> "null"
    this is String && this.contains('\n') -> """${'"'}""
${this.lines().map {" ".repeat(20) + "|" + it}.joinToString("\n")}
${" ".repeat(20)}""${'"'}.trimMargin()"""
    this is String && this.contains('"') -> """${'"'}${this.replace("\"","\\\"")}${'"'}"""
    this is Number -> this.toString()
    this is KSType -> /* I think this can only happen for enums */ this.declaration.qualifiedName!!.asString()
    this is ArrayList<*> && this.size == 0 -> "arrayOf()"
    this is ArrayList<*> -> """arrayOf(
${this.joinToString(prefix=" ".repeat(20), postfix = "\n") { it.asKotlinExpression() }}${" ".repeat(16)})"""
    else -> "${'"'}${this}${'"'}"
}
