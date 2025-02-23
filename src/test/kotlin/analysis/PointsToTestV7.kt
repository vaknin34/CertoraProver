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

        SolidityVersion.V7_0, SolidityVersion.V7_6
    ]
)
@Tag(EXPENSIVE)
class PointsToTestV7 : PointsToTest() {}
