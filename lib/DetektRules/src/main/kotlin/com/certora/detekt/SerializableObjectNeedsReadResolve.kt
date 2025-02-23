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
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.resolve.*
import org.jetbrains.kotlin.resolve.descriptorUtil.*
import org.jetbrains.kotlin.types.typeUtil.*

@RequiresTypeResolution
class SerializableObjectNeedsReadResolve(config: Config) : Rule(config) {

    override val issue = Issue(
        javaClass.simpleName,
        Severity.Defect,
        "Finds kotlin singleton objects which implement Serializable but do not have a correct readResolve method.",
        Debt.TWENTY_MINS
    )

    override fun visitObjectDeclaration(declaration: KtObjectDeclaration) {
        super.visitObjectDeclaration(declaration)

        // We're only interested in singleton "object" declarations, not anonymous classes.
        if (declaration.isObjectLiteral()) {
            return
        }

        // Only look at Serializable objects
        val objectDesc = bindingContext.getDescriptor(declaration) ?: return
        if (!objectDesc.implementsJavaSerializable) {
            return
        }

        // Does the object have a readResolve method?  Does it have the right signature?
        val correctReadResolve = objectDesc.findCorrectReadResolveMethod()
        val anyReadResolve = correctReadResolve ?: objectDesc.findAnyReadResolveMethod()
        when {
            anyReadResolve == null ->
                // No readResolve
                report(CodeSmell(
                    issue,
                    Entity.from(declaration.nameIdentifier ?: declaration),
                    "Serializable object missing 'readResolve' method.  Add 'private fun readResolve(): Any = ${declaration.name}'"
                ))
            correctReadResolve == null ->
                // Incorrect readResolve signature (the typical problem is that the return type is not 'Any')
                report(CodeSmell(
                    issue,
                    Entity.from(anyReadResolve.kotlinSource ?: declaration.nameIdentifier ?: declaration),
                    "Serializable object has 'readResolve' method with wrong signature.  It should be 'private fun readResolve(): Any"
                ))
            else -> {
                // Check that the body of the readResolve method only references this object.  The typical error
                // here is a copy-and-paste from another object, without updating the returned object.
                val readResolveSource = correctReadResolve.kotlinSource as KtFunction?
                readResolveSource?.bodyExpression?.accept(object : DetektVisitor() {
                    override fun visitReferenceExpression(expression: KtReferenceExpression) {
                        super.visitReferenceExpression(expression)
                        val refTarget = bindingContext[BindingContext.REFERENCE_TARGET, expression]
                            as? ClassDescriptor
                        val refTargetSource = refTarget?.kotlinSource
                        if (refTargetSource is KtObjectDeclaration && refTargetSource != declaration) {
                            report(CodeSmell(
                                issue,
                                Entity.from(expression),
                                "'readResolve' implementation should only reference ${declaration.name}"
                            ))
                        }
                    }
                })
            }
        }
    }

    companion object {
        /**
         * Look for any method named `readResolve`, directly declared in this object
         */
        fun ClassDescriptor.findAnyReadResolveMethod(): FunctionDescriptor? =
            findDeclaredFunction("readResolve", checkSuperClasses = false) { true }

        /**
         * Find a `readResolve` method with the correct signature:
         *
         *  ANY-ACCESS-MODIFIER fun readResolve(): Any
         *
         * Note that Java serialization will ignore `readResolve` if the return type is not `Object`, which in Kotlin
         * is either `Any` or `Any?`.
         */
        fun ClassDescriptor.findCorrectReadResolveMethod(): FunctionDescriptor? =
            findDeclaredFunction("readResolve", checkSuperClasses = false) {
                it.valueParameters.isEmpty() && it.typeParameters.isEmpty() &&
                it.returnType?.isAnyOrNullableAny() == true
            }

    }
}
