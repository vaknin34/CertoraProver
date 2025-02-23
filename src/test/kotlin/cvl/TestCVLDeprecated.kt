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

package cvl

import infra.CVLFlow
import org.junit.jupiter.api.Test
import kotlin.io.path.Path

class TestCVLDeprecated: AbstractCVLTest() {

    @Test
    fun testDeprecatedAliases() {
        val confPath = Path("src/test/resources/cvl/Quantifiers/badExample1/badExample1.conf")
        val primaryContractName = "test"
        val cvlText = """
            rule testDeprecatedAliases {
            static_require (2 > 1);
            static_assert (false);
        }
        """.trimIndent()
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(confPath, cvlText, primaryContractName), listOf(
                ExpType("static_require"), ExpType("static_assert")
        )
        )
    }

    @Test
    fun testDeprecatedInvokeFallback() {
        val confPath = Path("src/test/resources/cvl/Quantifiers/badExample1/badExample1.conf")
        val primaryContractName = "test"
        val cvlText = """
            rule check_fallback {
            env e;
            calldataarg arg;
            invoke_fallback(e, arg);
            assert true;
        }
        """.trimIndent()
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(confPath, cvlText, primaryContractName),
            listOf(ExpType("invoke_fallback"))
        )
    }
}
