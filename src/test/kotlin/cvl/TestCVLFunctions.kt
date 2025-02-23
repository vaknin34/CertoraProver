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

class TestCVLFunctions : AbstractCVLTest() {

    @Test
    fun testCVLTypechecking_CVLFunctions_Default() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLTypechecking/CVLFunctions/confExample/Default/Default.conf")),
            listOf(
                ExpType("h"), ExpType("g"), ExpType("g")
            )
        )
    }

    @Test
    fun testCVLTypechecking_CVLFunctions_Default2() {
        testFlowWithPredicatesCVLError(
            CVLFlow().getProverQuery(Path("src/test/resources/cvl/CVLTypechecking/CVLFunctions/confExample/Default2/Default2.conf")),
            listOf(
                ExpressionAt("bad/bad2.spec", 2, 2, "x"),
                ExpressionAt("bad/bad2.spec", 4, 4, "y"),
                GeneralType("bad/bad2.spec", 10, 10),
                GeneralType("bad/bad2.spec", 12, 12),
                GeneralType("bad/bad2.spec", 17, 17),
            )
        )
    }

}
