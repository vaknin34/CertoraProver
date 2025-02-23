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
import spec.cvlast.typechecker.NonBoolExpression
import kotlin.io.path.Path

class TestCVLImports: AbstractCVLTest() {
    @Test
    fun testImports1() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLSyntax/imports/badExample1/badExample1.conf")),
            listOf(
                SpecificType(NonBoolExpression::class, "c.spec", 7, 7)
            )
        )
    }

    @Test
    fun testImports2() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLSyntax/imports/badExample2/badExample2.conf")), listOf(
                GeneralType("import_rule_2.spec", 7, 7),
                GeneralType("b.spec", 10, 12),
                GeneralType("import_rule_2.spec", 10, 12)
            )
        )
    }

    @Test
    fun testImports3() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLSyntax/imports/badExample3/badExample3.conf")), listOf(
                GeneralType("import_rule_2.spec", 7, 7),
                GeneralType("b.spec", 10, 12),
                GeneralType("import_rule_2.spec", 10, 12)
            )
        )
    }

    @Test
    fun testImports4() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLSyntax/imports/badExample4/badExample4.conf")), listOf(
                GeneralType("import_rule_4.spec", 4, 9), GeneralType("d.spec", 0, 2)
            )
        )
    }

    @Test
    fun testImports5() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLSyntax/imports/badExample5/badExample5.conf")), listOf(
                GeneralType("nestedImport/e.spec", 0, 0),
                GeneralType("import_invariant.spec", 4, 4),
                GeneralType("import_invariant.spec", 6, 8)
            )
        )
    }

    @Test
    fun testImports6() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLSyntax/imports/badExample6/badExample6.conf")), listOf(
                GeneralType("import_invariant_1.spec", 4, 4),
                GeneralType("import_invariant_1.spec", 6, 6),
                GeneralType("import_invariant_1.spec", 6, 6)
            )
        )
    }

    @Test
    fun testImportsUsingSimple() {
        testNoErrors(
            CVLFlow().getProverQuery(Path("lib/Shared/src/test/resources/CERT4488/UsingSimple.conf"))
        )
    }
    @Test
    fun testImportsUsingTransitive() {
        testNoErrors(
            CVLFlow().getProverQuery(Path("lib/Shared/src/test/resources/CERT4488/UsingTransitive.conf"))
        )
    }

    @Test
    fun testImportsUsingClashingAliases() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("lib/Shared/src/test/resources/CERT4488/UsingClashingAliases.conf")),
            listOf(GeneralType("ImportedB.spec", 1, 1))
        )
    }
}
