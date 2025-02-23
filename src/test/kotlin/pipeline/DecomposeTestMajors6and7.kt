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

package pipeline

import annotation.ScopedVersions
import annotation.SolidityVersion
import annotation.SolidityVersions
import org.junit.jupiter.params.ParameterizedTest

@SolidityVersions(
    [
        SolidityVersion.V6_1,
        SolidityVersion.V6_6,
        SolidityVersion.V6_8,
        SolidityVersion.V6_10,
        SolidityVersion.V6_11,
        SolidityVersion.V6_12,
        SolidityVersion.V7_0
    ]
)
class DecomposeTestMajors6and7 : DecomposeTest() {
    override val FALLBACK: String
        get() = "fallback()"

    override fun IMMUTABLE(solc: String): String =
        if (solc == SolidityVersion.V6_1.compilerName()) {
            ""
        } else {
            "immutable"
        }


    @ParameterizedTest
    @ScopedVersions
    fun testAll(solc: String) {
        contractNoLoops().let { (src, exp) -> testHarness(solc, src, exp) }
        contractWithLoops1().let { (src, exp) -> testHarness(solc, src, exp) }
        contractWithLoops2().let { (src, exp) -> testHarness(solc, src, exp) }
        contractWithExplicityPayableFallback().let { (src, exp) -> testHarness(solc, src, exp) }
        contractWithExplicityPayableFallbackAndANonPayableFunction().let { (src, exp) ->
            testHarness(
                solc,
                src,
                exp
            )
        }
        contractWithExplicitPayableFallbackAndAPayableFunction().let { (src, exp) -> testHarness(solc, src, exp) }
        contractWithExplicitNonPayableFallbackAndAPayableFunction().let { (src, exp) ->
            testHarness(
                solc,
                src,
                exp
            )
        }
        contractWithExplicitNonPayableFallbackAndANonPayableFunction().let { (src, exp) ->
            testHarness(
                solc,
                src,
                exp
            )
        }
        withImmutable(solc).let { (src, exp) -> testHarness(solc, src, exp) }
    }
}