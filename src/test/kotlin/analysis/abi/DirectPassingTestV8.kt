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
import annotation.Z3Timeout
import annotations.TestTags.EXPENSIVE
import extension.ForceZ3Timeout
import extension.IgnoreZ3TimeoutErrors
import extension.WithConfigExtension
import org.junit.jupiter.api.Tag
import net.jqwik.api.Tag as JQWIK_TAG
import org.junit.jupiter.api.extension.ExtendWith

@SolidityConfigMatrix(
    solidityVersion = [
        // TODO CERT-5856
        // SolidityVersion.V8_1,
        // SolidityVersion.V8_11,
        SolidityVersion.V8_19
    ],
    withOptimizeFlag = false
)

@Tag(EXPENSIVE)
@ExtendWith(WithConfigExtension::class, IgnoreZ3TimeoutErrors::class)
@Z3Timeout(3000)
@ExtendWith(ForceZ3Timeout::class)
class DirectPassingTestV8: DirectPassingTest() {
    override val header = ""
}
