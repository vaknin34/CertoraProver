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

import org.junit.jupiter.params.provider.ArgumentsSource

@Target(AnnotationTarget.FUNCTION, AnnotationTarget.CLASS)
@Retention(AnnotationRetention.RUNTIME)
@ArgumentsSource(SolidityConfigMatrixConsumer::class)
annotation class SolidityConfigMatrix(
    val solidityVersion: Array<SolidityVersion> = [SolidityVersion.V6_10, SolidityVersion.V7_0, SolidityVersion.V6_12,
        SolidityVersion.V5_11, SolidityVersion.V7_6, SolidityVersion.V8_2, SolidityVersion.V8_9, SolidityVersion.V8_11,
        SolidityVersion.V8_13, SolidityVersion.V8_16],
    val withOptimizeFlag: Boolean = true,
    val withHeaders: Boolean = false,
    val headers: Array<String> = ["pragma experimental ABIEncoderV2;", ""],
)