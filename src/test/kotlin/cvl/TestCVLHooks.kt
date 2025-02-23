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

class TestCVLHooks : AbstractCVLTest() {

    @Test
    fun testHooks() {
        val confPath = Path("src/test/resources/cvl/Ghost/hooks/badExample1/badExample1.conf")
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(confPath), listOf(
                GeneralType("badExample1/hooks.spec", 8, 10),
                GeneralType("badExample1/hooks.spec", 12, 14),
                GeneralType("badExample1/hooks.spec", 21, 23),
                GeneralType("badExample1/hooks.spec", 25, 27)
        )
        )
    }

    //TODO: test should return errors CERT-1898
    @Test
    fun testHookWithIf() {
        val confPath = Path("src/test/resources/cvl/Ghost/hooks/badExample2/badExample2.conf")
        val primaryContractName = "Dummy"
        val cvlText = """
            sort foo;

            ghost ghostX(foo) returns uint256;

            ghost blaze(uint) returns uint {
                axiom forall uint256 x. blaze(x) == x;
            }

            hook Sstore (slot 0) uint i {
                uint256 my_collided_variable2 = i;
                if (my_collided_variable2 == 1) {
                    assert false;
                } else {
                    assert true;
                }
                havoc ghostX assuming forall foo x. ghostX@new(x) == blaze(my_collided_variable2);
            }
        """.trimIndent()
        testNoErrors(CVLFlow().getProverQuery(confPath, cvlText, primaryContractName))
    }

    @Test
    fun testHookWithBytesTypeParameter() {
        val confPath = Path("lib/Shared/src/test/resources/HashBlob/HookWithBytesType.conf")
        val primaryContractName = "HookWithBytesType"
        val cvlText = """
            hook Sload uint v currentContract.blerp[KEY bytes whatever] {
                assert whatever.length == 3;
            }

            hook Sstore currentContract.blerp[KEY bytes whatever] uint v {
                assert whatever.length == 3;
            }
        """.trimIndent()
        testNoErrors(CVLFlow().getProverQuery(confPath, cvlText, primaryContractName))
    }

    @Test
    fun testHookWithStringTypeParameter() {
        val confPath = Path("lib/Shared/src/test/resources/HashBlob/HookWithStringType.conf")
        val primaryContractName = "HookWithStringType"
        val cvlText = """
            hook Sload uint v currentContract.blerp[KEY string whatever] {
                assert whatever.length == 3;
            }

            hook Sstore currentContract.blerp[KEY string whatever] uint v {
                assert whatever.length == 3;
            }
        """.trimIndent()
        testNoErrors(CVLFlow().getProverQuery(confPath, cvlText, primaryContractName))
    }

    @Test
    fun testHookWithUIntType() {
        val confPath = Path("lib/Shared/src/test/resources/HashBlob/HookWithUintType.conf")
        val primaryContractName = "HookWithUintType"
        val cvlText = """
            hook Sload uint v currentContract.blerp[KEY uint256 whatever] {
                assert whatever == 3;
            }

        """.trimIndent()
        testNoErrors(CVLFlow().getProverQuery(confPath, cvlText, primaryContractName))
    }

}
