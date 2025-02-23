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

package smtlibutils.cmdprocessor

import kotlinx.coroutines.runBlocking
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import smtlibutils.data.FactorySmtScript.eq
import smtlibutils.data.FactorySmtScript.not
import smtlibutils.data.SMT
import smtlibutils.data.SmtScript
import smtlibutils.data.Sort
import kotlin.time.Duration
import kotlin.time.Duration.Companion.seconds

internal class CoreHelperTest {

    @Test
    fun assertCheckParseUnsatCore01() {
        val script = SmtScript()
        val x = script.id("x", Sort.IntSort)
        val y = script.id("y", Sort.IntSort)
        val z = script.id("z", Sort.IntSort)
        val smt = SMT(
            listOf(
                script.setLogic("ALL"),
                script.declareConst(x.id.sym, Sort.IntSort),
                script.declareConst(y.id.sym, Sort.IntSort),
                script.declareConst(z.id.sym, Sort.IntSort),
                script.assertCmd(x eq y),
                script.assertCmd(not(x eq y)),
                script.assertCmd(not(z eq y)),
            )
        )
        val formula = SmtFormula.fromSmt(smt)
        val conjunction = formula.conjunction
        val ucHelper = CoreHelper(conjunction, script)

        val query = SmtFormulaCheckerQuery(
            SmtFormulaCheckerQueryInfo("myFormula", getUnsatCore = true),
            formula,
            coreHelper = ucHelper,
        )

        val smtCheckResult = runBlocking {
            SimpleFormulaChecker.plainZ3Instance(
                3.seconds,
                script,
                CmdProcessor.Options.Default.copy(produceUnsatCores = true)
            ).check(query)
        }

        val expectation = conjunction.subList(0, 2)
        assertTrue(smtCheckResult.unsatCore?.nameToOriginal?.values?.containsAll(expectation) == true)
    }

}
