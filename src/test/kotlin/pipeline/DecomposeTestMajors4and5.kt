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
        SolidityVersion.V4_24,
        SolidityVersion.V4_25,
//        SolidityVersion.V5_2, // not in CI, but remember some changes in calldata handling between 5.2 and 5.3. Probably not critical.
        SolidityVersion.V5_3,
        SolidityVersion.V5_9,
        SolidityVersion.V5_11,
        SolidityVersion.V5_12
        //, SolidityVersion.V5_16 // weird issue with 5.16 about `Field 'sourceLocation' is required, but it was missing`
    ]
)
class DecomposeTestMajors4and5 : DecomposeTest() {

    override val FALLBACK: String
        get() = "function()"

    override fun IMMUTABLE(solc: String): String = error("No immutable in $solc")

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

    }
}