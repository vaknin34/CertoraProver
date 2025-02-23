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

package analysis.opt

import analysis.ExprView
import analysis.enarrow
import datastructures.stdcollections.*
import log.*
import tac.NBId
import tac.Tag
import vc.data.*
import vc.data.TACCmd.Simple.AssigningCmd.AssignExpCmd


private val logger = Logger(LoggerTypes.NEGATION_NORMALIZER)

/**
 * Aims to minimize the number of boolean negations in the program, (and does some inlining along the way). e.g.,
 * ```
 *    !!a ~~~> a
 *    !a \/ !b ~~~> !(a /\ b)
 *    !a /\ !b ~~~> !(a \/ b)
 *    jumpi(!cond, dst, elseDst) ~~~> jumpi(cond, elseDst, dst)
 *    ite(!cond, a, b) ~~~> ite(cond, b, a)
 * ```
 * This is meant to be very cheap and so works only block by block, and only when the code is in 3-address-form.
 * It does work in ascending order, and so these transformations can compose, e.g., this will happen:
 * ```
 *  !(!a \/ !b)   ~~~>  a /\ b
 * ```
 * There are two reasons to run this:
 *   1. It simplifies the code to improve readability, and may help the solvers (though probably slightly).
 *   2. It makes looking for specific patterns in the code easier, as it removes superfluous constructs.
 */
class NegationNormalizer(val code: CoreTACProgram) {

    private val g = code.analysisCache.graph
    private val txf = TACExprFactUntyped

    fun rewrite(): CoreTACProgram {
        val patcher = ConcurrentPatchingProgram(code)
        code.blockgraph.keys.parallelStream().forEach {
            BlockWorker(it, patcher).process()
        }
        logger.trace {
            patcher.debugPrinter().toString(code, javaClass.simpleName)
        }
        return patcher.toCode()
    }

    private inner class BlockWorker(val nbid: NBId, val patcher: ConcurrentPatchingProgram) {

        /** To simplify matters, we don't consider vars that are assigned more than one time in the block */
        private val doublyAssigned = g.lcmdSequence(nbid)
            .mapNotNull { it.cmd.getLhs() }
            .groupBy { it }
            .filter { it.value.size >= 2 }
            .keys

        // `negated[a] == b` means that `!a` can be replaced by `b`.
        private val negated = mutableMapOf<TACSymbol.Var, TACSymbol.Var>()

        /** Returns the furthest away equiv var */
        private fun equivPos(v: TACSymbol.Var): TACSymbol.Var {
            var current = v
            while (true) {
                current = negated[current]?.let { negated[it] }
                    ?: return current
            }
        }

        /** Returns the furthest away var that is a negation of [v] */
        private fun equivNeg(v: TACSymbol.Var) =
            negated[v]?.let(::equivPos)

        /** Returns the furthest away equiv var, with true if it is a negated equivalent */
        private fun equiv(v: TACSymbol.Var): Pair<TACSymbol.Var, Boolean> {
            var current = v
            var neg = false
            while (true) {
                current = negated[current]
                    ?: return current to neg
                neg = !neg
            }
        }


        private fun handleAssign(lcmd: ExprView<TACExpr>) {
            val e = lcmd.exp
            if (e is TACExpr.Sym) {
                if (e is TACExpr.Sym.Var) {
                    // if `x := y`, then `negated[x] := negated[y]`
                    negated[e.s]?.let {
                        negated[lcmd.lhs] = it
                    }
                }
                return
            }

            when (e) {
                is TACExpr.UnaryExp.LNot -> {
                    val o = (e.o as? TACExpr.Sym.Var)?.s
                        ?: return
                    equivNeg(o)?.let {
                        patcher.replace(lcmd.ptr, lcmd.cmd.copy(rhs = it.asSym()))
                    }
                    negated[lcmd.lhs] = o
                }

                is TACExpr.BinBoolOp -> {
                    val negs = e.ls
                        .map { it as? TACExpr.Sym.Var ?: return }
                        .map { equivNeg(it.s)?.asSym() ?: return }
                    val tempVar = patcher.newTempVar("neg", Tag.Bool)
                    negated[lcmd.lhs] = tempVar
                    patcher.replace(
                        lcmd.ptr,
                        listOf(
                            AssignExpCmd(
                                tempVar,
                                when (e) {
                                    is TACExpr.BinBoolOp.LAnd -> txf.LOr(negs)
                                    is TACExpr.BinBoolOp.LOr -> txf.LAnd(negs)
                                }
                            ),
                            lcmd.cmd.copy(rhs = txf.LNot(tempVar.asSym()))
                        )
                    )
                }

                is TACExpr.TernaryExp.Ite -> {
                    val cond = (e.i as? TACExpr.Sym.Var)?.s
                        ?: return
                    val (newCond, neg) = equiv(cond)
                    if (newCond != cond) {
                        patcher.replace(
                            lcmd.ptr,
                            lcmd.cmd.copy(
                                rhs = if (neg) {
                                    e.copy(i = newCond.asSym(), t = e.e, e = e.t)
                                } else {
                                    e.copy(i = newCond.asSym())
                                }
                            )
                        )
                    }
                }

                else -> Unit
            }
        }

        // check for reassignments
        fun process() {
            g.lcmdSequence(nbid).forEach { lcmd ->
                val (ptr, cmd) = lcmd
                if (cmd.getLhs() in doublyAssigned) {
                    return@forEach
                }
                when (cmd) {
                    is AssignExpCmd ->
                        handleAssign(lcmd.enarrow<TACExpr>())

                    is TACCmd.Simple.AssumeNotCmd ->
                        if (cmd.cond is TACSymbol.Var) {
                            equivNeg(cmd.cond)
                                ?.let { patcher.replace(ptr, TACCmd.Simple.AssumeCmd(it)) }
                                ?: run {
                                    val temp = patcher.newTempVar("neg", Tag.Bool)
                                    patcher.replace(ptr, listOf(
                                        AssignExpCmd(temp, txf.LNot(cmd.cond.asSym())),
                                        TACCmd.Simple.AssumeCmd(temp)
                                    ))
                                }
                        }

                    is TACCmd.Simple.JumpiCmd ->
                        (cmd.cond as? TACSymbol.Var)?.let(::equiv)?.let { (newCond, neg) ->
                            when {
                                newCond == cmd.cond -> Unit

                                neg -> {
                                    logger.debug { "Reversed jump condition: $ptr : $cmd" }
                                    patcher.replace(
                                        ptr,
                                        cmd.copy(cond = newCond, dst = cmd.elseDst, elseDst = cmd.dst)
                                    )
                                }

                                else -> {
                                    logger.debug { "inlined jump condition: $ptr : $cmd" }
                                    patcher.replace(ptr, cmd.copy(cond = newCond))
                                }
                            }
                        }

                    else -> Unit
                }
            }
        }
    }

}
