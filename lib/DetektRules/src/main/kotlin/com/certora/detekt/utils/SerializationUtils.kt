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

package com.certora.detekt.utils

import org.jetbrains.kotlin.descriptors.*
import org.jetbrains.kotlin.descriptors.annotations.*
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.resolve.descriptorUtil.*
import org.jetbrains.kotlin.types.*
import org.jetbrains.kotlin.types.typeUtil.*

val serializationAnnotations = setOf(
    FqName("kotlinx.serialization.Serializable"),
    FqName("kotlinx.serialization.Contextual"),
    FqName("kotlinx.serialization.Transient"),
    FqName("utils.KSerializable"),
    FqName("utils.KTransient"),
)

fun Annotations.getSerializableAnnotation(): AnnotationDescriptor? = firstOrNull { it.fqName in serializationAnnotations }
val ClassDescriptor.hasSerializableAnnotation get() = annotations.getSerializableAnnotation() != null
val Annotated.hasSerializableAnnotation get() = annotations.getSerializableAnnotation() != null

val ClassDescriptor.implementsHasKSerializable get() = implementsInterface(FqName("utils.HasKSerializable"))

val ClassDescriptor.needsSerializableAnnotation get() = when(kind) {
    ClassKind.INTERFACE -> false // @Serializable doesn't apply to interfaces
    ClassKind.ANNOTATION_CLASS -> false // @Serializable doesn't apply to annotations
    ClassKind.ENUM_CLASS -> false // Enums are always serializable (they are serialized by name)
    ClassKind.ENUM_ENTRY -> false // ibid
    else -> implementsHasKSerializable
}

val ClassDescriptor.implementsJavaSerializable get() = implementsInterface(FqName("java.io.Serializable"))
val KotlinType.isJavaSerializableClass get() = classDescriptor?.implementsJavaSerializable ?: false
