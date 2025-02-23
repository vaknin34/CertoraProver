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

package ksp

import com.google.devtools.ksp.KspExperimental
import com.google.devtools.ksp.containingFile
import com.google.devtools.ksp.getAnnotationsByType
import com.google.devtools.ksp.processing.Dependencies
import com.google.devtools.ksp.processing.Resolver
import com.google.devtools.ksp.symbol.KSAnnotated
import com.google.devtools.ksp.symbol.KSAnnotation
import com.google.devtools.ksp.symbol.KSClassDeclaration

/**
 * This function is very useful for when you statically know the class of the annotation that you want to process - it
 * unpacks the annotations into objects of that type, so you can just access the fields without bothering with dynamic
 * unpacking.  For example:
 *
 *     resolver.getAnnotations<KSClassDeclaration, ExampleClassAnnot>()
 *         .map { (classDecl : KSClassDeclaration, classAnnot : ExampleClassAnnot) -> ... }
 *
 * @return all elements of type [E] that are annotated with [A], along with the annotations.
 */
inline fun <reified E : KSAnnotated, reified A : Annotation> Resolver.getAnnotations() : List<Pair<E, A>> {
    return this.getSymbolsWithAnnotation(A::class.qualifiedName!!)
        .filterIsInstance<E>()
        .getAnnotations<E,A>()
        .toList()
}

/**
 * This function is useful for iterating over a specific set of elements instead of finding all annotated
 * elements (e.g. `classDecl.getDeclaredProperties().getAnnotations<PropAnnotation>()`)
 *
 * @return all elements of `this` annotated by [A], along with the annotations
 */
@OptIn(KspExperimental::class)
inline fun <E : KSAnnotated, reified A : Annotation> Sequence<E>.getAnnotations() : Sequence<Pair<E,A>> {
    return this.flatMap { element -> element.getAnnotationsByType(A::class).map { element to it }}
}

/**
 * This function is useful when you **don't** statically know the annotation you want to process - it just returns the
 * [KSAnnotation] objects without unpacking them.
 * @return all elements of type [E] that are annotated with annotation declared by [annotationDeclaration], along with the annotations.
 */
inline fun <reified E : KSAnnotated> Resolver.getAnnotations(
    annotationDeclaration: KSClassDeclaration
) : List<Pair<E, KSAnnotation>> {
    return this.getSymbolsWithAnnotation(annotationDeclaration.qualifiedName!!.asString())
        .filterIsInstance<E>()
        .flatMap { annotated ->
            annotated.annotations
                .filter { it.shortName == annotationDeclaration.simpleName && it.annotationType.resolve().declaration == annotationDeclaration }
                .map { annotated to it }
        }
        .toList()
}

/**
 * Convenience method for building a [Dependencies] object from a set of declarations returned by the resolver.
 */
fun dependencies(vararg annotateds : List<KSAnnotated>)
    = Dependencies(true, *annotateds.flatMap { it.mapNotNull { it.containingFile } }.toTypedArray())

/**
    Checks if an annotation is of a specific type.
 */
fun isAnnotation(
    it: KSAnnotation,
    shortName: String,
    qualified: String,
) = it.shortName.asString() == shortName &&
    it.annotationType.resolve().declaration.qualifiedName?.asString() == qualified

/**
    Checks if a declaration has a particular annotation.
 */
 fun KSAnnotated.hasAnnotation(
    shortName: String,
    qualified: String
) = this.annotations.any { isAnnotation(it, shortName, qualified) }

/**
    Gets the fully-qualified name of a class, including star-projected type arguments if needed.
 */
fun KSClassDeclaration.fullyQualifiedStarProjectedName() = qualifiedName?.asString()?.let { name ->
    if (typeParameters.isEmpty()) { name } else { "$name<${typeParameters.joinToString { "*" }}>" }
}

