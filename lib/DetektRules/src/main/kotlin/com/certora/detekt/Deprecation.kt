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

import io.gitlab.arturbosch.detekt.api.*
import io.gitlab.arturbosch.detekt.api.internal.RequiresTypeResolution
import org.jetbrains.kotlin.descriptors.ConstructorDescriptor
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.name.Name
import org.jetbrains.kotlin.psi.KtCallExpression
import org.jetbrains.kotlin.psi.KtReferenceExpression
import org.jetbrains.kotlin.resolve.BindingContext
import org.jetbrains.kotlin.resolve.descriptorUtil.fqNameSafe

/**
 * We use detekt to detect deprecation because we want to use the baseline functionality to grandfather in existing
 * uses.
 */
@RequiresTypeResolution
class Deprecation(config : Config) : Rule(config) {
    override val issue = Issue(
        javaClass.simpleName,
        Severity.Defect,
        "This rule detects uses of classes marked with @DetektDeprecated",
        Debt.TWENTY_MINS
    )

    override fun visitCallExpression(expression: KtCallExpression) {
        super.visitCallExpression(expression)

        val calleeRef = expression.calleeExpression as? KtReferenceExpression
            ?: return
        val callee = bindingContext[BindingContext.REFERENCE_TARGET, calleeRef] as? ConstructorDescriptor
            ?: return
        val annotation = callee.constructedClass.annotations.findAnnotation(FqName("utils.DetektDeprecatedClass"))
            ?: return

        report(CodeSmell(
            issue,
            Entity.from(calleeRef),
            "${callee.constructedClass.fqNameSafe} is deprecated; ${annotation.allValueArguments[Name.identifier("message")]?.value}"
        ))
    }
}
