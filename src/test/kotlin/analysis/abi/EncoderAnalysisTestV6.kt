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

package analysis.abi

import annotation.SolidityConfigMatrix
import annotation.SolidityVersion
import annotations.TestTags.EXPENSIVE
import extension.IgnoreZ3TimeoutErrors
import extension.WithConfigExtension
import org.junit.jupiter.api.extension.ExtendWith
import org.junit.jupiter.api.Tag

@SolidityConfigMatrix(
    solidityVersion = [
        SolidityVersion.V6_12, SolidityVersion.V6_1, SolidityVersion.V6_10, SolidityVersion.V6_11
    ],
    withOptimizeFlag = true
)
@ExtendWith(WithConfigExtension::class, IgnoreZ3TimeoutErrors::class)
@Tag(EXPENSIVE)
class EncoderAnalysisTestV6 : EncoderAnalysisTest() {
    override val header = "pragma experimental ABIEncoderV2;"
}
