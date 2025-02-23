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

@RequiresTypeResolution
class KSerializableBaseClassRequirements(config: Config) : Rule(config) {

    override val issue = Issue(
        javaClass.simpleName,
        Severity.Warning,
        "Finds serializable base classes which don't guarantee subclasses are serializable.",
        Debt.TWENTY_MINS
    )

    override fun visitClass(clazz: KtClass) {
        super.visitClassOrObject(clazz)

        val desc = bindingContext.getDescriptor(clazz) ?: return

        if (desc.kind == ClassKind.CLASS && desc.modality != Modality.FINAL) {
            if (desc.hasSerializableAnnotation && !desc.implementsHasKSerializable) {
                report(CodeSmell(
                    issue,
                    Entity.from(clazz.nameIdentifier ?: clazz),
                    "${desc.name} is a Kotlin-serializable base class, and must implement HasKSerializable to ensure all subclasses are serializable."
                ))
            }
        }
    }
}
