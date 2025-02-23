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

package sbf

import sbf.domains.*
import org.junit.jupiter.api.Test
import org.junit.jupiter.api.Assertions
import log.*

class LinearExpressionTest {

    @Test
    fun test01() {
        // To see the logger
        System.setProperty(LoggerTypes.SBF.toLevelProp(), "info")

        val vfac = VariableFactory()
        val x = vfac.get("x")
        val y = vfac.get("y")
        val z = vfac.get("z")

        val e1 = LinearExpression(x) sub ExpressionNum(1)
        sbfLogger.info {"$e1"}
        val e2 = e1.substitute(x, y)
        sbfLogger.info {"After renaming $x with $y: $e2"}
        val e3 = e2.substitute(y, z)
        sbfLogger.info {"After renaming $y with $z: $e3"}
        val e4 = e3.eval(z, ExpressionNum(1))
        sbfLogger.info {"After evaluating $z with 1: $e4\nOld expressions: $e1\n$e2\n$e3"}
        Assertions.assertEquals(true, e4 == LinearExpression(ExpressionNum(0)))
    }

    @Test
    fun test02() {
        // To see the logger
        System.setProperty(LoggerTypes.SBF.toLevelProp(), "info")

        val vfac = VariableFactory()
        val x = vfac.get("x")
        val y = vfac.get("y")
        val z = vfac.get("z")

        // Create linear constraint 2*x + 3*y - 3*z - 5
        val e1 = LinearExpression(x, ExpressionNum(2)) add
                LinearExpression(y, ExpressionNum(3)) sub
                LinearExpression(z, ExpressionNum(3)) sub ExpressionNum(5)

        val e2 = e1.eval(x, ExpressionNum(2)).eval(y, ExpressionNum(3)).eval(z, ExpressionNum(3))
        sbfLogger.info {"After evaluating $e1 with $x=2, $y=3 $z=3: $e2"}
        Assertions.assertEquals(true, e2 == LinearExpression(ExpressionNum(-1)))
    }

    @Test
    fun test03() {
        // To see the logger
        System.setProperty(LoggerTypes.SBF.toLevelProp(), "info")

        val vfac = VariableFactory()
        val x = vfac.get("x")
        val e1 = LinearExpression(x, ExpressionNum(0)) // 0*x = 0
        val e2 = LinearExpression(x, ExpressionNum(1)) // 1*x = x

        sbfLogger.info {"Creating $e1 and $e2"}
    }
}
