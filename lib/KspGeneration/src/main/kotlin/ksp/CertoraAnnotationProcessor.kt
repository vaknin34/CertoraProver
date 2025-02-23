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

import com.google.devtools.ksp.symbol.KSAnnotated
import com.google.devtools.ksp.symbol.KSAnnotation

interface CertoraAnnotationProcessor {

    val annotationPackage: String

    fun KSAnnotation.isAnnotation(shortName: String) = isAnnotation(this, shortName, "$annotationPackage.$shortName")

    fun KSAnnotated.hasAnnotation(shortName: String) = this.annotations.any {
        it.isAnnotation(shortName)
    }

    fun isAnnotation(
        it: KSAnnotation,
        shortName: String,
        qualified: String,
    ): Boolean = it.shortName.asString() == shortName && it.annotationType.resolve().declaration.qualifiedName?.asString() == qualified

}
