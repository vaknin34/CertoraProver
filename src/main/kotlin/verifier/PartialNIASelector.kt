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

import analysis.CmdPointer
import com.certora.collect.*
import datastructures.stdcollections.mutableSetOf
import smt.solverscript.functionsymbols.NonSMTInterpretedFunctionSymbol
import smt.solverscript.functionsymbols.TheoryFunctionSymbol
import vc.data.*
import vc.data.lexpression.META_CMD_PTR
import vc.gen.LExpVC

/**
 * An interface for deciding whether [LExpression] should be represented using LIA,
 * or kept precise and represented by NIA.
 */
interface LIASelector {
    /**
     * Methods returns true if [lExp] should be represented by LIA, otherwise it returns false, i.e., [lExp] should
     * be represented by NIA.
     */
    fun selectLIA(lExp: LExpression): Boolean = true
}

/** A trivial selector, always returns true. */
object TakeAllSelector : LIASelector

/** A trivial selector, always returns false. */
object TakeNoneSelector : LIASelector {

    override fun selectLIA(lExp: LExpression): Boolean = false
}

/**
 * Selector based on distance of a multiplication (TACExpression) from an assert.
 * The selector firstly precomputes set of all multiplications which are in the given [depth] from any assert
 * by performing BFS over [lExpVc.vcTacCommandGraph] starting from all assert commands.
 * Then where the method [selectLIA] is called for a multiplication it returns true if the command is not in the computed
 * set (and should be represented using LIA), or is in the set and should be represented by NIA.
 * For example, consider a path: commands Cmd1: x = a*b; Cmd2: y = x + c; Cmd3: z = y + d; Assert z > 0,
 * the multiplication a*b from Cmd1 would be kept precise when [depth] is at least 3.
 * When [finishBfs] is set to true, it performs BFS over the whole graph to determine its total depth.
 */
class CloseToAssertSelector(
    val lExpVc: LExpVC, val ruleName: String, val depth: Int, finishBfs: Boolean = false
) : LIASelector {
    var selectorKeepNIAFrequency: Int = 0
    var selectorAllMulFrequency: Int = 0

    private val graph = lExpVc.vcTacCommandGraph

    private val cmdsInDepth: MutableSet<CmdPointer> = mutableSetOf()

    var graphDepth = 0

    /**
     * init performs breadth-first search over [graph] of program to the depth defined by [depth]
     * from all asserts. It saves all CmdPointer of multiplication operations within the given depth
     * to [cmdsInDepth] what is later used by the [select] method to determine which [LExpression] should be NIA.
     * If [finishBfs] is set true, it always travels the whole [graph] to determine its total depth (but
     * only commands in the given [depth] from any assert are saved to [cmdsInDepts]).
     * [finishBfs] is used to get the depth of the whole TAC graph so we can compare it with [depth] and
     * use the information for evaluation of PartialLIA approach.
     */
    init {
        val queue: ArrayDeque<CmdPointer> = ArrayDeque(graph.blocks.flatMap { block ->
            block.commands.mapNotNull {
                if (it.cmd !is TACCmd.Simple.AssertCmd) {
                    null
                } else {
                    it.ptr
                }
            }
        })
        check(!queue.isEmpty()) { "Queue in PartialSelector should not be empty at the beginning" }

        val visitedCommands = mutableSetOf<CmdPointer>()

        var actLevel = 0

        while (!queue.isEmpty() && (actLevel <= depth || finishBfs)) {
            val levelSize = queue.size

            repeat(levelSize) {
                val actCmdPtr =
                    queue.removeFirstOrNull() ?: error("Queue in PartialSelector should not be empty at this point")
                visitedCommands += actCmdPtr
                val simpleCmd = graph.elab(actCmdPtr)

                if (simpleCmd.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd &&
                    (simpleCmd.cmd.rhs is TACExpr.Vec.Mul || simpleCmd.cmd.rhs is TACExpr.Vec.IntMul) &&
                    actLevel <= depth
                ) {
                    cmdsInDepth.add(actCmdPtr)
                }

                simpleCmd.cmd.getRhs().filterIsInstance<TACSymbol.Var>().forEach { tacSymbol ->
                    graph.cache.def.defSitesOf(tacSymbol, actCmdPtr)
                        .filterNot { it in visitedCommands }
                        .forEach { queue.addLast(it) }
                }
            }

            actLevel++
        }

        graphDepth = actLevel
    }

    companion object {
        internal fun isNonLinear(lExp: LExpression): Boolean {
            return lExp is LExpression.ApplyExpr.Binary &&
                (lExp.f is TheoryFunctionSymbol.Vec.IntMul || lExp.f is NonSMTInterpretedFunctionSymbol.Vec.Mul)
        }
    }

    override fun selectLIA(lExp: LExpression): Boolean {
        if (!isNonLinear(lExp)) {
            return true
        }

        /** Add 1 to the count of multiplications considered by the selector. */
        selectorAllMulFrequency++

        val cmdPtr = lExp.meta[META_CMD_PTR] ?: return true
        if (cmdPtr in cmdsInDepth) {
            selectorKeepNIAFrequency++
        }

        return cmdPtr !in cmdsInDepth
    }
}
