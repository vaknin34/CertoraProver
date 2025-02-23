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

package verifier

import analysis.TACCommandGraph
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.Test
import smt.solverscript.LExpressionFactory
import statistics.data.TACProgramMetadata
import vc.data.LExpression
import vc.data.TACBuilderAuxiliaries
import vc.data.TACCmd
import vc.data.TACProgramBuilder
import vc.data.lexpression.META_CMD_PTR
import vc.gen.LExpVC
import vc.gen.LeinoWP

object PartialSelectorTest : TACBuilderAuxiliaries() {

    private val testProgName = RuleAndSplitIdentifier.dummyRoot("testProg")


    private fun getMultiplications(lExpressions: Sequence<LExpression>): Sequence<LExpression> =
        lExpressions.filter { lExp ->
            CloseToAssertSelector.isNonLinear(lExp)
        }

    private fun checkTrueSelects(
        mulExprs: Sequence<LExpression>,
        graph: TACCommandGraph,
        selector: CloseToAssertSelector,
        trueMulLabel: (TACCmd.Simple) -> Boolean
    ) {
        mulExprs.forEach {
            val tacCmd = graph.elab(it.meta[META_CMD_PTR] ?: error("ApplyExpr should have CommandPtr")).cmd
            if (trueMulLabel(tacCmd)) {
                assertTrue(!selector.selectLIA(it))
            } else if (tacCmd is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
                assertTrue(selector.selectLIA(it))
            }
        }
    }

    @Test
    fun basicTest() {
        val prog = TACProgramBuilder {
            a assign Mul(number(1), number(2))
            b assign Mul(number(1), number(3))
            c assign Mul(aS, bS)
            label("d")
            d assign Mul(cS, number(3))
            x assign Gt(dS, number(0))
            assert(x)
        }

        val vc: LExpVC = LeinoWP(
            prog.code,
            LExpressionFactory(),
            TACProgramMetadata(testProgName)
        ).generateVCs()

        checkTrueSelects(
            getMultiplications(vc.subExpressionsSequence()),
            TACCommandGraph(prog.code),
            CloseToAssertSelector(vc, "", 2)
        ) { tacCmd -> tacCmd == prog.cmd("d") }
    }

    @Test
    fun emptySelect() {
        val prog = TACProgramBuilder {
            a assign Mul(number(1), number(2))
            b assign Mul(number(1), number(3))
            c assign Mul(aS, bS)
            d assign Add(cS, number(3))
            x assign Gt(dS, number(0))
            assert(x)
        }

        val vc: LExpVC =
            LeinoWP(prog.code, LExpressionFactory(), TACProgramMetadata(testProgName)).generateVCs()

        checkTrueSelects(
            getMultiplications(vc.subExpressionsSequence()),
            TACCommandGraph(prog.code),
            CloseToAssertSelector(vc, "", 2)
        ) { _ -> false }
    }

    @Test
    fun uninitVars() {
        val prog = TACProgramBuilder {
            a assign Mul(bS, cS)
            b assign Mul(bS, aS)
            c assign Mul(aS, bS)
            x assign Gt(cS, number(0))
            assert(x)
        }
        val vc: LExpVC =
            LeinoWP(prog.code, LExpressionFactory(), TACProgramMetadata(testProgName)).generateVCs()

        checkTrueSelects(
            getMultiplications(vc.subExpressionsSequence()),
            TACCommandGraph(prog.code),
            CloseToAssertSelector(vc, "", 4)
        ) { _ -> true }
    }

    @Test
    fun distantMul() {
        val prog = TACProgramBuilder {
            label("a")
            a assign Mul(number(4), number(5))
            b assign aS
            c assign bS
            d assign cS
            x assign Gt(dS, number(0))
            assert(x)
        }
        val vc: LExpVC =
            LeinoWP(prog.code, LExpressionFactory(), TACProgramMetadata(testProgName)).generateVCs()

        checkTrueSelects(
            getMultiplications(vc.subExpressionsSequence()),
            TACCommandGraph(prog.code),
            CloseToAssertSelector(vc, "", 5)
        ) { tacCmd -> tacCmd == prog.cmd("a") }
    }

    @Test
    fun finishBfs() {
        val prog = TACProgramBuilder {
            val e = bv256Var("d")
            a assign Mul(number(1), number(52))
            b assign Mul(number(2), number(5))
            c assign Mul(number(7), number(6))
            d assign Mul(aS, bS)
            e assign Mul(dS, cS)
            x assign Gt(e.asSym(), number(0))
            assert(x)
        }

        val vc: LExpVC =
            LeinoWP(prog.code, LExpressionFactory(), TACProgramMetadata(testProgName)).generateVCs()

        val selector = CloseToAssertSelector(vc, "", 2)
        val selector1 = CloseToAssertSelector(vc, "", 2, true)
        assertTrue(selector.graphDepth < selector1.graphDepth)
        assertTrue(selector1.graphDepth == 5)
    }

    @Test
    fun basicIntMul() {
        val prog = TACProgramBuilder {
            i assign IntMul(number(1), number(2))
            j assign IntMul(number(1), number(3))
            k assign IntMul(iS, jS)
            label("s")
            s assign IntMul(kS, number(3))
            x assign Gt(sS, number(0))
            assert(x)
        }
        val vc: LExpVC =
            LeinoWP(prog.code, LExpressionFactory(), TACProgramMetadata(testProgName)).generateVCs()

        checkTrueSelects(
            getMultiplications(vc.subExpressionsSequence()),
            TACCommandGraph(prog.code),
            CloseToAssertSelector(vc, "", 2)
        ) { tacCmd -> tacCmd == prog.cmd("s") }
    }
}
