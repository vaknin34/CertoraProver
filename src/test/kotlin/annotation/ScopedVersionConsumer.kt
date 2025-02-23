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
import org.junit.jupiter.params.provider.ArgumentsProvider
import org.junit.jupiter.params.support.AnnotationConsumer
import java.util.stream.Stream


class ScopedVersionConsumer : ArgumentsProvider, AnnotationConsumer<ScopedVersions>, OptimizeFlagAnnotationConsumer {
    override fun provideArguments(context: ExtensionContext?): Stream<out Arguments> {
        val withOptimizedFlag = hasOptimizerFlag(context!!)
        return context.testClass?.map {
            it.annotations.firstOrNull {
                it is SolidityVersions
            }?.let { it as SolidityVersions }?.versions?.flatMap {ver ->
                toMatrix(ver.compilerName(), withOptimizedFlag)
            }?.stream()
        }?.orElse(null) ?: throw IllegalArgumentException("Did not find SolidityVersions annotation on parent class")
    }

    override fun accept(t: ScopedVersions?) {
    }

}
