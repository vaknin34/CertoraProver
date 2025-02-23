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
import org.jetbrains.kotlin.descriptors.ClassDescriptor
import org.jetbrains.kotlin.psi.*
import org.jetbrains.kotlin.resolve.descriptorUtil.*

@RequiresTypeResolution
class MustHaveKSerializable(config: Config) : Rule(config) {

    override val issue = Issue(
        javaClass.simpleName,
        Severity.Defect,
        "Finds classes which implement HasKSerializable but are not correctly annotated.",
        Debt.TWENTY_MINS
    )

    override fun visitClassOrObject(classOrObject: KtClassOrObject) {
        super.visitClassOrObject(classOrObject)

        val desc = bindingContext.getDescriptor(classOrObject) ?: return

        if (desc.needsSerializableAnnotation && !desc.hasSerializableAnnotation) {
            report(CodeSmell(
                issue,
                Entity.from(classOrObject.nameIdentifier ?: classOrObject),
                "${desc.name} implements HasKSerializable, so should be annotated with @KSerializable."
            ))
        }
    }
}
