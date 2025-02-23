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

package analysis

import annotation.SolidityVersion
import annotation.SolidityVersions
import annotations.TestTags.EXPENSIVE
import org.junit.jupiter.api.Tag

@SolidityVersions(
    [
        SolidityVersion.V6_1, SolidityVersion.V6_8,
        SolidityVersion.V6_12, SolidityVersion.V6_10
    ]
)
@Tag(EXPENSIVE)
class PointsToTestV6 : PointsToTest() {
    override fun testRawCallWithReturn(solc: String, optimize: Boolean) {
        if(solc == SolidityVersion.V6_1.compilerName()) {
            // syntax isn't supported for this version
            return
        }
    }
}
