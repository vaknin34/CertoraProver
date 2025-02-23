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
import spec.cvlast.typechecker.ToCVLTypeError
import kotlin.io.path.Path

class TestCVLGhost: AbstractCVLTest() {

    @Test
    fun testGhost1() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/Ghost/badExample1/badExample1.conf")),
            listOf(
                ExpType("g1"),
                ExpType("f1"),
            )
        )
    }

    @Test
    fun testGhost2() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/Ghost/badExample2/badExample2.conf")), listOf(
                SpecificType(ToCVLTypeError::class, "badExample2/badSpecs2.spec", 4, 7)
            )
        )
    }

    @Test
    fun testGhost3() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/Ghost/badExample3/badExample3.conf")), listOf(
                GeneralType("badExample3/badSpecs3.spec", 18, 18),
                ExpType("g1"),
                ExpType("f1"),
                LhsType("undefinedVar"),
                GeneralType("badExample3/badSpecs3.spec", 7, 7),
            )
        )
    }

    /** Check that ghosts _can_ be updated by assignment */
    @Test
    fun testGhostShadowingAssignment() {
        val confPath = Path("src/test/resources/cvl/Ghost/badExample3/badExample3.conf") // doesn't really matter, just need something
        val primaryContractName = "Dummy"
        val cvlText = """
            ghost uint g;
            rule notShadowing {
                g = 0; // this is also considered a "DefinitionCmd", but this should be OK to do with a ghost.
                assert g == 0;
                havoc g assuming g@new != 0; // multiple assignments/havocs are also OK for a ghost
                assert g != 0;
            }
        """.trimIndent()
        testFlowWithPredicatesCVL(
            CVLFlow().getProverQuery(confPath, cvlText, primaryContractName), listOf()
        )
    }
}
