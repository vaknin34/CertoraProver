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
import spec.cvlast.typechecker.CVLError
import java.util.function.Predicate
import kotlin.io.path.Path

class TestDirectStorage : AbstractCVLTest() {
    private fun runTest(cvlText: String, f: (CVLError) -> Boolean) {
        runTest(cvlText, Predicate(f))
    }

    private fun runTest(cvlText: String, f: Predicate<CVLError>) {
        runTest(cvlText, listOf(f))
    }

    private fun runTest(cvlText: String, preds: List<Predicate<CVLError>>) {
        val confPath = Path("src/test/resources/cvl/CVLCompilation/DirectStorageAccess/Default.conf")
        val primaryContractName = "Test"
        testFlowWithPredicatesCVLError(CVLFlow().getProverQuery(confPath, cvlText, primaryContractName), preds)
    }


    @Test
    fun testWrongMappingType() {
        runTest("""
            using Test as t;

            rule bad_thing {
               uint wrong_type;
               uint96 x = t.a[wrong_type][wrong_type].baz;
               assert true;
            }
        """.trimIndent()) {
            it is CVLError.Exp && it.exp.toString().contains("wrong_type")
        }
    }

    @Test
    fun testWrongAccessType() {
        runTest("""
            using Test as t;

            rule bad1 {
               address x;
               uint a1 = t.topLevel1.nonsense;
               uint a2 = t.a.nonsense;
               uint a3 = t.a[x][0][1];
               uint a4 = t.a.length;
            }
        """.trimIndent(), listOf(
            ExpType(
                "t.topLevel1.nonsense"
            ),
            ExpType(
                "t.a.nonsense"
            ),
            ExpType("t.a[x][0][1]"),
            ExpType("t.a.length")
        ))
    }

    @Test
    fun testCannotIndexIntoBytes() {
        runTest("""
            using Test as t;
            rule bad {
               bytes1 b = t.theBytes[0];
               assert true;
           }
        """.trimIndent(), ExpType("t.theBytes[0]"))
    }

    @Test
    fun testIncorrectStaticIndexType() {
        runTest(
            """
                using Test as t;
                rule bad {
                    address k;
                    uint fine;
                    uint96 v = t.a[k][k].gorp[fine];
                    assert v == 0;
               }
            """.trimIndent()
        , ErrorContaining(4, "Expected index expression to be convertible to uint256, got address"))
    }

    @Test
    fun testIncorrectDynamicIndexType() {
        runTest(
            """
                using Test as t;
                rule bad {
                    address k;
                    uint fine;
                    uint96 v = t.a[k][fine].gorp[k];
                    assert v == 0;
               }
            """.trimIndent()
            , ErrorContaining(4, "Expected index expression to be convertible to uint256, got address"))
    }

    @Test
    fun testNonsenseTopLevelField() {
        runTest("""
            using Test as t;

            rule bad {
               uint z = t.doesNotExist;
               assert true;
            }
        """.trimIndent(), ExpType("t.doesNotExist"))
    }

    @Test
    fun nonExistentStructfield() {
        runTest("""
            using Test as t;
            rule bad {
               bytes x;
               string y;
               uint z = t.nestedMap[x][y].foo.doesNotExist;
               assert true;
            }
        """.trimIndent(), ExpType("t.nestedMap[x][y].foo.doesNotExist"))
    }

    @Test
    fun testIncorrectOutputType1() {
        runTest("""
            using Test as t;
            rule bad {
               bool blah = t.topLevel1;
            }
        """.trimIndent(), ErrorContaining(2, "has type `uint24` (from the VM)"))
    }

    @Test
    fun testInconvertibleType1() {
        runTest("""
            using Test as t;
            rule bad {
                bytes x;
                string y;
                Test.InnerStruct s = t.nestedMap[x][y].foo;
                assert true;
            }
        """.trimIndent(), ErrorContaining(4, "has type `Test.InnerStruct` (from the VM)"))
    }

    @Test
    fun testInconvertibleType2() {
        runTest("""
            using Test as t;

            rule bad {
               address x;
               bool[] z = t.a[x][0].bar;
               assert z.length == 0;
            }
        """.trimIndent(), ErrorContaining(4, "has type `bool[]` (from the VM)"))
    }

    @Test
    fun testNoStaticArrayLengths() {
        runTest("""
            using Test as t;

            rule bad {
               address x;
               uint l = t.a[x].length;
               assert l == 6;
            }
        """.trimIndent(), ExpType("t.a[x].length"))
    }
}
