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

package normalizer

import annotation.SolidityVersion
import annotation.SolidityVersions
import annotation.WithOptimizedFlag

import org.junit.jupiter.api.Test
import org.junit.jupiter.params.ParameterizedTest

class CanonicalTranslationTableSlimmedTest : CanonicalTranslationTableTest() {
    //TODO: override whatever tests you want from CanonicalTranslationTableTest and
    //      annotate them accordingly :)
    //      Example:

    @ParameterizedTest
    @SolidityVersions(
        [SolidityVersion.V8_13]
    )
    @WithOptimizedFlag
    override fun testDigestChangeOnReplaceDivWithSub(solc: String, optimize: Boolean) =
        super.testDigestChangeOnReplaceDivWithSub(solc, optimize)
}
