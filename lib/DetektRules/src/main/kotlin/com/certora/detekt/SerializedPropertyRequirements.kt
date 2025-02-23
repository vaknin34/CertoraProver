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

package com.certora.detekt

import com.certora.detekt.utils.*
import io.gitlab.arturbosch.detekt.api.*
import io.gitlab.arturbosch.detekt.api.internal.RequiresTypeResolution
import org.jetbrains.kotlin.descriptors.*
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.psi.psiUtil.*
import org.jetbrains.kotlin.resolve.*
import org.jetbrains.kotlin.resolve.descriptorUtil.*
import org.jetbrains.kotlin.types.*
import org.jetbrains.kotlin.types.typeUtil.*

@RequiresTypeResolution
class SerializedPropertyRequirements(config: Config) : Rule(config) {

    override val issue = Issue(
        javaClass.simpleName,
        Severity.Warning,
        "Finds serialized properties whose values are not guaranteed to be serializable.",
        Debt.TWENTY_MINS
    )

    override fun visitPrimaryConstructor(constructor: KtPrimaryConstructor) {
        super.visitPrimaryConstructor(constructor);

        val classDesc = bindingContext.getDescriptor(constructor.getContainingClassOrObject()) ?: return
        if (!classDesc.isConcreteClass) {
            return
        }

        // skip the class if it has no Serializable annotation *or* it has one with arguments specifying a serializer
        val annot = classDesc.annotations.getSerializableAnnotation()
        if (annot == null || annot.allValueArguments.isNotEmpty()) {
            return
        }

        for (param in constructor.getValueParameters().filter { it.isPropertyParameter() }) {
            val propertyDesc = bindingContext[BindingContext.VALUE_PARAMETER, param]?.let {
                bindingContext[BindingContext.VALUE_PARAMETER_AS_PROPERTY, it as ValueParameterDescriptor]
            }
            if (propertyDesc?.hasSerializableAnnotation == false) {
                findUnserializableInterface(propertyDesc.type)?.let {
                    report(CodeSmell(
                        issue,
                        Entity.from(param ?: constructor),
                        "Type $it may not be serializable. " +
                            "Use a class, or an interface that inherits from utils.HasKSerializable, " +
                            "or provide a custom serializer."
                    ))
                }
            }
        }
    }

    companion object {
        private val knownSerializableCollections = setOf(
            FqName("kotlin.collections.List"),
            FqName("kotlin.collections.Map"),
            FqName("kotlin.collections.Map.Entry"),
            FqName("kotlin.collections.Set"),
            FqName("kotlin.collections.MutableList"),
            FqName("kotlin.collections.MutableMap"),
            FqName("kotlin.collections.MutableMap.Entry"),
            FqName("kotlin.collections.MutableSet"),
        )

        private fun findUnserializableInterface(type: KotlinType): KotlinType? = when {
            type.isError -> null // Avoid false positives for unresolvable types
            type.isCapturedStarProjection -> null
            serializationAnnotations.any { type.isAnnotatedTypeArgument(it) } -> null
            type.hasSupertype(FqName("utils.HasKSerializable")) -> null
            else -> type.classDescriptor.let { desc ->
                when {
                    desc == null -> type
                    !desc.isInterface -> null
                    desc.fqNameSafe in knownSerializableCollections ->
                        type.arguments.asSequence().filter { !it.isStarProjection }
                        .mapNotNull { findUnserializableInterface(it.type) }
                        .firstOrNull()
                    else -> type
                }
            }
        }
    }
}
