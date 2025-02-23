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

package analysis.skeyannotation

import analysis.*
import io.mockk.mockk
import org.junit.jupiter.api.Test
import scene.IScene
import tac.StartBlock
import tac.Tag
import vc.data.*
import vc.data.TACCmd.Simple.AssigningCmd.AssignExpCmd
import vc.data.codeFromListOfCommands
import java.math.BigInteger

internal class ExpDataflowAnalysisTest {


    class MaybeOne private constructor(val maybeOne: Boolean) {
        companion object {
            val True = MaybeOne(true)
            val False = MaybeOne(false)
            operator fun invoke(maybeOne: Boolean) = if (maybeOne) True else False
        }
    }

    object MaybeOneLattice : JoinLattice<MaybeOne> {
        override fun join(x: MaybeOne, y: MaybeOne): MaybeOne = MaybeOne(x.maybeOne || y.maybeOne)
        override fun equiv(x: MaybeOne, y: MaybeOne): Boolean = x == y
        val bottom = MaybeOne.False
    }

    val txf = TACExprFactUntyped

    @Test
    fun testIteFunctionality() {
        val x = TACSymbol.Var("x", Tag.Bit256)
        val y = TACSymbol.Var("y", Tag.Bit256)
        val z = TACSymbol.Var("z", Tag.Bit256)
        val tac = codeFromListOfCommands(
            StartBlock,
            listOf(
                AssignExpCmd(x, TACSymbol.lift(0)),
                AssignExpCmd(y, TACSymbol.lift(1)),
                AssignExpCmd(z, txf { ite(True, x.asSym(), y.asSym()) }),
            ),
            name = "testIte",
        )
        val analysis = object : ExpDataflowAnalysis<MaybeOne>(
            TACCommandGraph(tac.transformToCore(mockk<IScene>())),
            MaybeOneLattice,
            MaybeOneLattice.bottom,
            ExpDirection.FORWARD
        ) {
            init {
                runAnalysis()
            }

            override fun stepExp(inState: List<MaybeOne>, exp: LTACExp): MaybeOne {
                return when (val e = exp.exp) {
                    is TACExpr.Sym.Const -> MaybeOne(e.s.value == BigInteger.ONE)
                    is TACExpr.TernaryExp.Ite -> handleIte(inState)
                    else -> join(inState)
                }
            }


            fun res(expPointer: ExpPointer) = expOut[expPointer]
        }

        val thirdCmdPtr = CmdPointer(StartBlock, pos = 2)
        val zLhsPtr = ExpPointer(thirdCmdPtr, ExpPointer.Path(0))

        assert(analysis.res(zLhsPtr) == MaybeOne.True)
    }
}
