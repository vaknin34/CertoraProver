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
import org.junit.jupiter.api.Assertions.*
import org.junit.jupiter.api.Test
import scene.ProverQuery
import spec.cvlast.typechecker.CVLError
import utils.CollectingResult
import utils.CollectingResult.Companion.mapErrors
import kotlin.io.path.Path

class SatisfyInRuleCheckerTest : AbstractCVLTest() {
    private val satisfyInCallInCallCVLText = """
        methods {
            function yalla(uint x) external returns bool envfree;
        }

        function first(uint x, uint y) {
            second(x, y);
        }

        function second(uint x, uint y) {
            if (x < y) {
                assert true;
            } else {
                satisfy x == y;
            }
        }

        function third(uint x, uint y) returns uint {
            second(x, y);
            return y;
        }


    """.trimIndent()

    private fun runTest(cvlText: String): CollectingResult<ProverQuery, CVLError> {
        val confPath = Path("src/test/resources/cvl/Example/goodExample/goodExample.conf")
        val primaryContractName = "dummy"
        val flow = CVLFlow()
        val res = flow.getProverQuery(confPath, cvlText, primaryContractName)
        return res
    }

    private fun runTestWithExpected(cvlText: String, vararg expectedMsgs: String) {
        val res = runTest(cvlText)

        if (expectedMsgs.isEmpty()) {
            assert(res.errorOrNull() == null
            ) { "Expecting correct cvl, but received the errors: ${res.errorOrNull()!!.map { it.message + it.location }}}" }
        } else {
            val errors = res.errorOrNull()
            assertTrue(errors != null) {"Expecting errors, got none"}
            assert(errors!!.size == expectedMsgs.size) { "Expecting a ${expectedMsgs.size} errors, got: ${res.mapErrors { it.display() }}" }
            for ((expected, err) in expectedMsgs.zip(errors)) {
                assertTrue(expected in err.message) {"Expecting $expected in message, got: ${err.display()}"}
            }
        }
    }

    @Test
    fun testSatisfyInCallInCallOk() {
        val cvlText = satisfyInCallInCallCVLText + """
            rule s {
                uint y;
                second(3, y);
            }
        """.trimIndent()
        runTestWithExpected(cvlText)
    }

    @Test
    fun testSatisfyInCallInCallInRequire() {
        val cvlText = satisfyInCallInCallCVLText + """
            rule s {
                uint y;
                require third(4, y) == y;
                assert true;
            }
        """.trimIndent()
        runTestWithExpected(cvlText, "require")
    }

    @Test
    fun testSatisfyInCallInCallInAssert() {
        val cvlText = satisfyInCallInCallCVLText + """
            rule s {
                uint y;
                assert third(4, y) == y;
            }
        """.trimIndent()
        runTestWithExpected(cvlText, "assert")
    }

    @Test
    fun testSatisfyInCallInCallInSatisfy() {
        val cvlText = satisfyInCallInCallCVLText + """
            rule s {
                uint y;
                satisfy third(4, y) == y;
            }
        """.trimIndent()
        runTestWithExpected(cvlText, "satisfy")
    }

    @Test
    fun testSatisfyInCallInInv() {
        val cvlText = satisfyInCallInCallCVLText + """
            invariant s(uint x) third(x, 1) == 1;
        """.trimIndent()
        val res = runTest(cvlText)
        assertTrue(res.errorOrNull() != null)
        assertTrue(res.errorOrNull()!!.any { "invariant" in it.message })
    }

    @Test
    fun testSatisfyInGhost() {
        val cvlText = satisfyInCallInCallCVLText + """
            ghost uint s {
                axiom s > third(s, s);
            }

        """.trimIndent()
        runTestWithExpected(cvlText, "ghost")
    }

    @Test
    fun testSatisfyInDefInRule() {
        val cvlText = satisfyInCallInCallCVLText + """
            definition profX returns uint = third(3,4);

            rule rouge(uint x) {
                uint z = profX();
                assert x < z;
            }
        """.trimIndent()
        runTestWithExpected(cvlText)
    }

    /**
     * Testing that a def containing satisfy will fail in a bad location
     */
    @Test
    fun testSatisfyInDefInAssertInRule() {
        val cvlText = satisfyInCallInCallCVLText + """
            definition profX returns uint = third(3,4);

            rule rouge(uint x) {
                assert x < profX();
            }
        """.trimIndent()
        runTestWithExpected(cvlText, "assert")
    }

    @Test
    fun testSatisfyInCallInCallInForallExp() {
        val cvlText = satisfyInCallInCallCVLText + """
            rule curry(uint x) {
                bool pgiaa = forall uint p. p < third(p, x);
                bool baain = exists uint p. p < third(p, x);
                assert true;
            }
        """.trimIndent()
        runTestWithExpected(cvlText, "quantified", "quantified")
    }

    @Test
    fun testSatisfyInCallInHavocAssumeExp() {
        val cvlText = satisfyInCallInCallCVLText + """
            ghost uint z;

            rule howard(uint x) {
                havoc z assuming third(x, x) > 1;
                assert true;
            }
        """.trimIndent()
        runTestWithExpected(cvlText, "assume")
    }

    @Test
    fun testSatisfyNestedInPreserved() {
        val cvlText = satisfyInCallInCallCVLText + """
            invariant s(uint x) x < 10
            {
                preserved {
                    if (x == 0) {
                        require x < 9;
                    } else {
                        satisfy true;
                    }
                }

                preserved yalla(uint y) {
                    if (y == 0) {
                        require x < 9;
                    } else {
                        satisfy y == x;
                    }
                }
            }
        """.trimIndent()
        runTestWithExpected(cvlText, "preserved", "preserved")
    }

    @Test
    fun testSatisfyInNestedInHook() {
        val cvlText = satisfyInCallInCallCVLText + """
            hook Sload uint y x {
                if (y > 3) {
                    satisfy y > 100;
                } else {
                    assert true;
                }
            }
        """.trimIndent()
        val confPath = Path("src/test/resources/cvl/Example/withStorage/withVar.conf")
        val primaryContractName = "withVar"
        val flow = CVLFlow()
        val res = flow.getProverQuery(confPath, cvlText, primaryContractName)
        val errors = res.errorOrNull()
        assertTrue(errors != null) {"Expecting errors, got none"}
        assert(errors!!.size == 1) { "Expecting 1 error, got: ${res.mapErrors { it.display() }}" }
        assertTrue("hook" in errors.first().message) {"Expecting hook in message, got: ${errors.first().display()}"}
    }

    @Test
    fun testSatisfyInCallInSummary() {
        val cvlText = """
            methods {
                function yalla(uint x) external returns (bool) envfree => bai(x);
            }

            function bai(uint x) returns bool {
                satisfy x == 0;
                return x > 0;
            }

            rule howard(uint x) {
                yalla(x);
                assert true;
            }
        """.trimIndent()
        runTestWithExpected(cvlText, "summaries")
    }
}
