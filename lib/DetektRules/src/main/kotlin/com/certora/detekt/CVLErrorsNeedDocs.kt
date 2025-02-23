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

import com.certora.detekt.utils.getDescriptor
import com.certora.detekt.utils.implementsInterface
import com.certora.detekt.utils.isConcreteClass
import io.gitlab.arturbosch.detekt.api.*
import io.gitlab.arturbosch.detekt.api.internal.RequiresTypeResolution
import org.jetbrains.kotlin.name.FqName
import org.jetbrains.kotlin.psi.KtClassOrObject

/**
 * This rule ensures that every subclass of [CVLError] has a [CVLErrorType] annotation (for documentation) and a
 * [CVLErrorExample] annotation (for documentation and testing).
 */
@RequiresTypeResolution
class CVLErrorsNeedDocs(config: Config) : Rule(config) {
    override val issue = Issue(
        javaClass.simpleName,
        Severity.Defect,
        "This rule detects CVLError subtypes that are not annotated with @CVLErrorType and @CVLErrorExample. " +
            "These annotations are used to generate user-facing documentation, examples, and tests.",
        Debt.TWENTY_MINS
    )

    override fun visitClassOrObject(classOrObject: KtClassOrObject) {
        super.visitClassOrObject(classOrObject)
        val desc = bindingContext.getDescriptor(classOrObject) ?: return
        if (!desc.isConcreteClass || !desc.implementsInterface(FqName("spec.cvlast.typechecker.CVLError"))) {
            return
        }
        if (!desc.annotations.hasAnnotation(FqName("spec.cvlast.typechecker.CVLErrorType"))) {
            report(CodeSmell(
                issue,
                Entity.Companion.from(classOrObject.nameIdentifier ?: classOrObject),
                "All subtypes of CVLError must be annotated with @CVLErrorType"
            ))
        }

        // TODO CERT-3231
        // Note that this should also be updated to require at least one example that has an expected message
        // if (!desc.annotations.hasAnnotation(FqName("spec.cvlast.typechecker.CVLErrorExample"))) {
        //     report(CodeSmell(
        //         issue,
        //         Entity.Companion.from(classOrObject.nameIdentifier ?: classOrObject),
        //         "All subtypes of CVLError must be annotated with @CVLErrorExample"
        //     ))
        // }
    }
}
