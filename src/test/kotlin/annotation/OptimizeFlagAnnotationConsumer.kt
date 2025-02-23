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

package annotation

import org.junit.jupiter.api.extension.ExtensionContext
import org.junit.jupiter.params.provider.Arguments

interface OptimizeFlagAnnotationConsumer {
    fun hasOptimizerFlag(context: ExtensionContext) : Boolean = context.element?.takeIf { it.isPresent }?.get()?.annotations?.any {
        it.annotationClass.java == WithOptimizedFlag::class.java
    } ?: false

    fun toMatrix(ver: SolidityVersion, hasOptimizedFlag: Boolean) : List<Arguments> = toMatrixOfAny(ver, hasOptimizedFlag)
    fun toMatrix(ver: String, hasOptimizedFlag: Boolean) : List<Arguments> = toMatrixOfAny(ver, hasOptimizedFlag)
}

private fun toMatrixOfAny(ver: Any, hasOptimizedFlag: Boolean) : List<Arguments> =
    if(hasOptimizedFlag) {
        listOf(true, false).map {
            Arguments.of(ver, it)
        }
    } else {
        listOf(Arguments.of(ver))
    }
