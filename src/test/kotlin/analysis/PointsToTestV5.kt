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
        SolidityVersion.ANY_5, SolidityVersion.V5_16, SolidityVersion.V5_12
    ]
)
@Tag(EXPENSIVE)
class PointsToTestV5 : PointsToTest() {
    override fun testTryCatch(solc: String, optimize: Boolean) {
        // syntax of this test isn't supported
        return
    }

    override fun testTryCatchWithDecode(solc: String, optimize: Boolean) {
        // the syntax of this test isn't supported
        return
    }

    override fun testRawCallWithReturn(solc: String, optimize: Boolean) {
        // the syntax of this test isn't supported
        return
    }
}
