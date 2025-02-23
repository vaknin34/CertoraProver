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

package smtlibutils.data

import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import utils.LazyCrossProduct

internal class LogicTest {

    @Test
    fun t01() {
        val onOrOff: List<List<String>> = listOf("QF_", "A", "UF", "DT").map { listOf(it, "") }
        val arithmetics = listOf(listOf("LIA", "NIA", "LRA", "NRA", "LIRA", "NIRA", "BV", ""))
        try {
            LazyCrossProduct(onOrOff + arithmetics).forEach {
                val string = it.joinToString("")
                val logic = Logic.fromString(string)
                println("successfully built logic $logic from string $string")
                if (string == "") {
                    assertTrue(logic == Logic.QF_CORE)
                } else {
                    containmentChecks(string, logic)
                }
            }
        } catch (e: Exception) {
            assertTrue(false, "failed to build logic")
        }
    }

    private fun containmentChecks(inputString: String, logic: Logic) {
        checkQf(inputString, logic)
        checkA(inputString, logic)
        checkUF(inputString, logic)
        checkDT(inputString, logic)
    }

    private fun checkQf(inputString: String, logic: Logic) {
        assertTrue(inputString.startsWith("QF_") == LogicFeature.Quantifiers !in logic.logicFeatures)
    }

    private fun checkA(inputString: String, logic: Logic) {
        val s = inputString.substringBefore("LIA")
            .substringBefore("NIA")
            .substringBefore("LRA")
            .substringBefore("NRA")
            .substringBefore("LIRA")
            .substringBefore("NIRA")
        assertTrue("A" in s == LogicFeature.Arrays in logic.logicFeatures)
    }

    private fun checkDT(inputString: String, logic: Logic) {
        assertTrue("DT" in inputString == LogicFeature.DataTypes in logic.logicFeatures)
    }

    private fun checkUF(inputString: String, logic: Logic) {
        assertTrue("UF" in inputString == LogicFeature.UninterpretedFunctions in logic.logicFeatures)
    }

}