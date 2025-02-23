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

package decompiler

import annotation.ScopedVersions
import annotation.SolidityVersion
import annotation.SolidityVersions
import org.junit.jupiter.params.ParameterizedTest

@SolidityVersions([
    SolidityVersion.V8_16
])
class BmcUnrollLabelsTestSlim : BmcUnrollLabelsTest() {
    @ParameterizedTest
    @ScopedVersions
    fun simpleLoop(solc: String) {
        super.templateSimpleLoop(solc)
    }


    @ParameterizedTest
    @ScopedVersions
    fun simpleReturn(solc: String) {
        super.templateSimpleReturn(solc)
    }

    @ParameterizedTest
    @ScopedVersions
    fun simpleReturn2(solc: String) {
        super.templateSimpleReturn2(solc)
    }

    @ParameterizedTest
    @ScopedVersions
    fun simpleBreak(solc: String) {
        super.templateSimpleBreak(solc)
    }

    @ParameterizedTest
    @ScopedVersions
    fun simpleRevert(solc: String) {
        super.templateSimpleRevert(solc)
    }

    @ParameterizedTest
    @ScopedVersions
    fun nestedLoop(solc: String) {
        super.templateNestedLoop(solc)
    }

    @ParameterizedTest
    @ScopedVersions
    fun nestedLoopWithRevert(solc: String) {
        super.templateNestedLoopWithRevert(solc)
    }

    @ParameterizedTest
    @ScopedVersions
    fun twoLoops(solc: String) {
        super.templateTwoLoops(solc)
    }
}
