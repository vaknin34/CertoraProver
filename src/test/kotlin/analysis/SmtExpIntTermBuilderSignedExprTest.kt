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

package analysis.smtblaster

import evm.MAX_EVM_INT256
import evm.MAX_EVM_UINT256
import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import smtlibutils.cmdprocessor.SmtQueryProcessor
import smtlibutils.cmdprocessor.SolverInstanceInfo
import smtlibutils.data.*
import java.math.BigInteger
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

class SmtExpIntTermBuilderSignedExprTest {

    companion object {
        val script = SmtScript()
        val solver1 = runBlocking {
            SmtQueryProcessor.fromSolverInstanceInfo(
                SolverInstanceInfo.plainZ3(10.seconds),
                FactorySmtScript,
                "s1script.smt2"
            )
        }

        private fun constructEq(functionBuilder: (SmtExp, SmtExp) -> SmtExp, trueOrFalseExp: SmtExp, num1: BigInteger, num2: BigInteger) =
                script.eq(trueOrFalseExp, functionBuilder(SmtExpIntTermBuilder.const(num1), SmtExpIntTermBuilder.const(num2)))
    }

    @Test
    fun testSlt() {
        val inputConjunction = listOf(
                constructEq(SmtExpIntTermBuilder::slt, script.True, BigInteger.ZERO, BigInteger.ONE),
                constructEq(SmtExpIntTermBuilder::slt, script.True, BigInteger.ZERO, MAX_EVM_INT256),
                constructEq(SmtExpIntTermBuilder::slt, script.False, BigInteger.ONE, BigInteger.ZERO),
                constructEq(SmtExpIntTermBuilder::slt, script.False, BigInteger.ONE, BigInteger.ONE),

                constructEq(SmtExpIntTermBuilder::slt, script.True, MAX_EVM_INT256.add(BigInteger.ONE), MAX_EVM_INT256.add(BigInteger.TWO)),
                constructEq(SmtExpIntTermBuilder::slt, script.True, MAX_EVM_INT256.add(BigInteger.ONE), MAX_EVM_UINT256),
                constructEq(SmtExpIntTermBuilder::slt, script.False, MAX_EVM_UINT256, MAX_EVM_INT256.add(BigInteger.ONE)),

                constructEq(SmtExpIntTermBuilder::slt, script.True, MAX_EVM_INT256.add(BigInteger.ONE), BigInteger.ZERO),
                constructEq(SmtExpIntTermBuilder::slt, script.True, MAX_EVM_UINT256, BigInteger.ZERO),
                constructEq(SmtExpIntTermBuilder::slt, script.False, BigInteger.ZERO, MAX_EVM_UINT256),
                constructEq(SmtExpIntTermBuilder::slt, script.False, BigInteger.ONE, MAX_EVM_INT256.add(BigInteger.ONE))
        )

        val result = runBlocking {
            solver1.check(inputConjunction, listOf(), null)
            solver1.checkSat()
        }

        Assertions.assertTrue(result == SatResult.SAT, "SmtExpIntTermBuilderSignedExprTest:" +
                "                                                        Failed while evaluating SLT expressions")
    }

    @Test
    fun testSle() {
        val inputConjunction = listOf(
                // both positive, i.e. <= MAX_EVM_INT256
                constructEq(SmtExpIntTermBuilder::sle, script.True, BigInteger.ZERO, BigInteger.ONE),
                constructEq(SmtExpIntTermBuilder::sle, script.True, BigInteger.ZERO, MAX_EVM_INT256),
                constructEq(SmtExpIntTermBuilder::sle, script.True, BigInteger.ONE, BigInteger.ONE),
                constructEq(SmtExpIntTermBuilder::sle, script.False, BigInteger.ONE, BigInteger.ZERO),
                constructEq(SmtExpIntTermBuilder::sle, script.False, BigInteger.TEN, BigInteger.TWO),

                // both negative, i.e. > MAX_EVM_INT256
                constructEq(SmtExpIntTermBuilder::sle, script.True, MAX_EVM_INT256.add(BigInteger.ONE), MAX_EVM_INT256.add(BigInteger.ONE)),
                constructEq(SmtExpIntTermBuilder::sle, script.True, MAX_EVM_INT256.add(BigInteger.ONE), MAX_EVM_INT256.add(BigInteger.TWO)),
                constructEq(SmtExpIntTermBuilder::sle, script.True, MAX_EVM_INT256.add(BigInteger.ONE), MAX_EVM_UINT256),
                constructEq(SmtExpIntTermBuilder::sle, script.False, MAX_EVM_UINT256, MAX_EVM_INT256.add(BigInteger.ONE)),

                // one positive & one negative
                constructEq(SmtExpIntTermBuilder::sle, script.True, MAX_EVM_INT256.add(BigInteger.ONE), BigInteger.ZERO),
                constructEq(SmtExpIntTermBuilder::sle, script.True, MAX_EVM_UINT256, BigInteger.ZERO),
                constructEq(SmtExpIntTermBuilder::sle, script.False, BigInteger.ZERO, MAX_EVM_UINT256),
                constructEq(SmtExpIntTermBuilder::sle, script.False, BigInteger.ONE, MAX_EVM_INT256.add(BigInteger.ONE))
        )

        val result = runBlocking {
            solver1.check(inputConjunction, listOf(), null)
            solver1.checkSat()
        }

        Assertions.assertTrue(result == SatResult.SAT, "SmtExpIntTermBuilderSignedExprTest:" +
                "                                                        Failed while evaluating SLE expressions")
    }

    @Test
    fun testSgt() {
        val inputConjunction = listOf(
                // both positive, i.e. <= MAX_EVM_INT256
                constructEq(SmtExpIntTermBuilder::sgt, script.True, BigInteger.ONE, BigInteger.ZERO),
                constructEq(SmtExpIntTermBuilder::sgt, script.True, MAX_EVM_INT256, BigInteger.ONE),
                constructEq(SmtExpIntTermBuilder::sgt, script.False, BigInteger.ONE, BigInteger.ONE),
                constructEq(SmtExpIntTermBuilder::sgt, script.False, BigInteger.ZERO, BigInteger.ONE),
                constructEq(SmtExpIntTermBuilder::sgt, script.False, BigInteger.ZERO, MAX_EVM_INT256),

                // both negative, i.e. > MAX_EVM_INT256
                constructEq(SmtExpIntTermBuilder::sgt, script.True, MAX_EVM_INT256.add(BigInteger.TWO), MAX_EVM_INT256.add(BigInteger.ONE)),
                constructEq(SmtExpIntTermBuilder::sgt, script.True, MAX_EVM_UINT256, MAX_EVM_INT256.add(BigInteger.ONE)),
                constructEq(SmtExpIntTermBuilder::sgt, script.False, MAX_EVM_INT256.add(BigInteger.ONE), MAX_EVM_UINT256),
                constructEq(SmtExpIntTermBuilder::sgt, script.False, MAX_EVM_UINT256, MAX_EVM_UINT256),

                // one positive & one negative
                constructEq(SmtExpIntTermBuilder::sgt, script.True, BigInteger.ZERO, MAX_EVM_INT256.add(BigInteger.ONE)),
                constructEq(SmtExpIntTermBuilder::sgt, script.True, BigInteger.ZERO, MAX_EVM_UINT256),
                constructEq(SmtExpIntTermBuilder::sgt, script.False, MAX_EVM_UINT256, BigInteger.ZERO),
                constructEq(SmtExpIntTermBuilder::sgt, script.False, MAX_EVM_INT256.add(BigInteger.ONE), BigInteger.ONE)
        )

        val result = runBlocking {
            solver1.check(inputConjunction, listOf(), null)
            solver1.checkSat()
        }

        Assertions.assertTrue(result == SatResult.SAT, "SmtExpIntTermBuilderSignedExprTest:" +
                "                                                        Failed while evaluating SGT expressions")
    }

    @Test
    fun testSge() {
        val inputConjunction = listOf(
                // both positive, i.e. <= MAX_EVM_INT256
                constructEq(SmtExpIntTermBuilder::sge, script.True, BigInteger.ONE, BigInteger.ZERO),
                constructEq(SmtExpIntTermBuilder::sge, script.True, MAX_EVM_INT256, BigInteger.ONE),
                constructEq(SmtExpIntTermBuilder::sge, script.True, BigInteger.ONE, BigInteger.ONE),
                constructEq(SmtExpIntTermBuilder::sge, script.False, BigInteger.ZERO, BigInteger.ONE),
                constructEq(SmtExpIntTermBuilder::sge, script.False, BigInteger.ZERO, MAX_EVM_INT256),

                // both negative, i.e. > MAX_EVM_INT256
                constructEq(SmtExpIntTermBuilder::sge, script.True, MAX_EVM_INT256.add(BigInteger.TWO), MAX_EVM_INT256.add(BigInteger.ONE)),
                constructEq(SmtExpIntTermBuilder::sge, script.True, MAX_EVM_UINT256, MAX_EVM_INT256.add(BigInteger.ONE)),
                constructEq(SmtExpIntTermBuilder::sge, script.True, MAX_EVM_UINT256, MAX_EVM_UINT256),
                constructEq(SmtExpIntTermBuilder::sge, script.False, MAX_EVM_INT256.add(BigInteger.ONE), MAX_EVM_UINT256),

                // one positive & one neg`ative
                constructEq(SmtExpIntTermBuilder::sge, script.True, BigInteger.ZERO, MAX_EVM_INT256.add(BigInteger.ONE)),
                constructEq(SmtExpIntTermBuilder::sge, script.True, BigInteger.ZERO, MAX_EVM_UINT256),
                constructEq(SmtExpIntTermBuilder::sge, script.False, MAX_EVM_UINT256, BigInteger.ZERO),
                constructEq(SmtExpIntTermBuilder::sge, script.False, MAX_EVM_INT256.add(BigInteger.ONE), BigInteger.ONE)
        )

        val result = runBlocking {
            solver1.check(inputConjunction, listOf(), null)
            solver1.checkSat()
        }

        Assertions.assertTrue(result == SatResult.SAT, "SmtExpIntTermBuilderSignedExprTest:" +
        "                                                                Failed while evaluating SGE expressions")
    }

}
