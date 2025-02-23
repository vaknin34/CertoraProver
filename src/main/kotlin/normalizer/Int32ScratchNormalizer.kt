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

package normalizer

import analysis.*
import analysis.CommandWithRequiredDecls.Companion.withDecls
import datastructures.stdcollections.*
import evm.*
import kotlin.streams.*
import tac.*
import utils.*
import vc.data.*
import java.math.BigInteger

/**
    Some Solidity exception handling produces code like this:

    ```
        ByteLongCopy 0x0 0x0 0x4 tacM:bytemap tacReturndata:bytemap
    ```
    (and then later it reads from tacM0x0 and shifts right to get the error selector).

    This confuses the pointer analysis due to the unsafe write to the first 4 bytes of memory, so we replace it with
    this:

    ```
        tacM0x0 = *
        ret = returndata[0x0]
        eq1 = tacM0x0 & 0xffffffff000...000
        eq2 = ret & 0xffffffff000...000
        eq3 = eq1 == eq2
        assume eq3
    ```
 */
object Int32ScratchNormalizer {

    private val MASK = TACSymbol.Const(0xffffffff.toBigInteger() shl 224)

    private fun replacement(): CommandWithRequiredDecls<TACCmd.Simple> {
        val ret = TACKeyword.TMP(Tag.Bit256, "!ret").toUnique("!")
        val eq1 = TACKeyword.TMP(Tag.Bit256, "!eq1").toUnique("!")
        val eq2 = TACKeyword.TMP(Tag.Bit256, "!eq2").toUnique("!")
        val eq3 = TACKeyword.TMP(Tag.Bool, "!eq3").toUnique("!")

        return listOf(
            TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                lhs = TACKeyword.MEM0.toVar()
            ),
            TACCmd.Simple.AssigningCmd.ByteLoad(
                lhs = ret,
                loc = TACSymbol.Zero,
                base = TACKeyword.RETURNDATA.toVar()
            ),
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = eq1,
                rhs = TACExpr.BinOp.BWAnd(
                    TACKeyword.MEM0.toVar().asSym(),
                    MASK.asSym()
                )
            ),
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = eq2,
                rhs = TACExpr.BinOp.BWAnd(
                    ret.asSym(),
                    MASK.asSym()
                )
            ),
            TACCmd.Simple.AssigningCmd.AssignExpCmd(
                lhs = eq3,
                rhs = TACExpr.BinRel.Eq(
                    eq1.asSym(),
                    eq2.asSym()
                )
            ),
            TACCmd.Simple.AssumeCmd(
                eq3
            )
        ).withDecls(ret, eq1, eq2, eq3)
    }

    fun rewrite(c: CoreTACProgram): CoreTACProgram {
        val graph = c.analysisCache.graph
        val constantAnalysis = MustBeConstantAnalysis(graph, NonTrivialDefAnalysis(graph))

        val matches = graph.commands.parallelStream().mapNotNull {
            it.maybeNarrow<TACCmd.Simple.ByteLongCopy>()?.takeIf {
                constantAnalysis.mustBeConstantAt(it.ptr, it.cmd.dstOffset) == BigInteger.ZERO &&
                constantAnalysis.mustBeConstantAt(it.ptr, it.cmd.srcOffset) == BigInteger.ZERO &&
                constantAnalysis.mustBeConstantAt(it.ptr, it.cmd.length) == DEFAULT_SIGHASH_SIZE &&
                it.cmd.dstBase == TACKeyword.MEMORY.toVar() &&
                it.cmd.srcBase == TACKeyword.RETURNDATA.toVar()
            }
        }.asSequence()

        return c.patching { patching ->
            matches.forEach { orig ->
                patching.replaceCommand(orig.ptr, replacement())
            }
        }
    }
}
