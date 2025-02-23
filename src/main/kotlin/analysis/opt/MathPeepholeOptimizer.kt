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

import analysis.*
import analysis.numeric.MAX_UINT
import utils.mapNotNull
import utils.parallelStream
import vc.data.*
import vc.data.SimplePatchingProgram.Companion.patchForEach
import java.math.BigInteger
import datastructures.stdcollections.*

object MathPeepholeOptimizer {
    fun trivialShiftSimplifier(c: CoreTACProgram) : CoreTACProgram {
        return c.parallelLtacStream().mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.takeIf {
                val rhs = it.cmd.rhs
                rhs is TACExpr.BinOp.ShiftRightLogical && rhs.o2 is TACExpr.Sym.Const && rhs.o2.s.value == BigInteger.ZERO
            }
        }.map {
            it.wrapped.enarrow<TACExpr.BinOp.ShiftRightLogical>()
        }.patchForEach(c, check = true) {
            this.replaceCommand(it.ptr, listOf(
                it.cmd.copy(
                    rhs = it.exp.o1
                )
            ))
        }
    }

    fun trivialSubtractionSimplifier(c: CoreTACProgram) : CoreTACProgram {
        /*
         * Replace
         * v = v1 - v2
         * where v1 must equal v2 with
         * v = 0
        */
        val rewrite = c.toPatchingProgram()
        c.analysisCache.graph.commands.parallelStream().filter {
            it.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && it.cmd.rhs is TACExpr.BinOp.Sub && it.cmd.rhs.operandsAreSyms() &&
                it.cmd.rhs.o1 is TACExpr.Sym.Var && it.cmd.rhs.o2 is TACExpr.Sym.Var
        }.map {
            it.enarrow<TACExpr.BinOp.Sub>()
        }.filter {
            val o1 = (it.exp.o1 as TACExpr.Sym.Var).s
            val o2 = (it.exp.o2 as TACExpr.Sym.Var).s
            o2 in c.analysisCache.gvn.findCopiesAt(it.ptr, it.ptr to o1)
        }.sequential().forEach {
            rewrite.replaceCommand(
                it.ptr, datastructures.stdcollections.listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        it.lhs,
                        TACSymbol.Zero.asSym(),
                        it.cmd.meta
                    )
                )
            )
        }
        return rewrite.toCode(c)
    }

    fun subtractionAsAddSimplifier(c: CoreTACProgram) : CoreTACProgram {
        /*
         * Replace
         * v = v1 + ~31 or v = ~31 + v1
         * with
         * v = v1 - 32
         */
        val rewrite = c.toPatchingProgram()
        val mustBeConstantAnalysis = MustBeConstantAnalysis(
            c.analysisCache.graph,
            wrapped = NonTrivialDefAnalysis(graph = c.analysisCache.graph)
        )
        fun isConstAt(t: TACExpr, l: LTACCmd) : BigInteger? {
            if(t !is TACExpr.Sym) {
                return null
            }
            return mustBeConstantAnalysis.mustBeConstantAt(l.ptr, t.s)
        }
        fun isSubtractionAsAdd(t: TACExpr, l: LTACCmd): Boolean {
            val k = isConstAt(t, l) ?: return false
            /*
              This is chosen heuristically based on what we've seen solidity use to "optimize" subtraction (that is, subtracting
              k by adding the twos complement encoding)
             */
            return k > BigInteger("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00", 16)
        }
        c.analysisCache.graph.commands.parallelStream().filter {
            it.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && it.cmd.rhs is TACExpr.Vec.Add && it.cmd.rhs.operandsAreSyms() &&
                (isSubtractionAsAdd(it.cmd.rhs.o1, it) || isSubtractionAsAdd(it.cmd.rhs.o2, it))
        }.map {
            it.enarrow<TACExpr.Vec.Add>()
        }.sequential().forEach { it ->
            val (subFrom, largeConst) = if(isSubtractionAsAdd(it.exp.o1, it.wrapped)) {
                it.exp.o2 to isConstAt(it.exp.o1, it.wrapped)!!
            } else {
                it.exp.o1 to isConstAt(it.exp.o2, it.wrapped)!!
            }
            val toSubtract = MAX_UINT.andNot(largeConst).plus(BigInteger.ONE)
            rewrite.replaceCommand(it.ptr, datastructures.stdcollections.listOf(
                TACCmd.Simple.AssigningCmd.AssignExpCmd(
                    lhs = it.lhs,
                    rhs = TACExpr.BinOp.Sub(subFrom, toSubtract.asTACSymbol().asSym()),
                    meta = it.cmd.meta
                )
            )
            )
        }
        return rewrite.toCode(c)
    }
}
