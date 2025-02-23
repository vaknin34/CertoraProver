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

package instrumentation.calls

import analysis.CmdPointer
import analysis.PatternDSL
import analysis.PatternMatcher
import analysis.icfg.ExpressionSimplifier
import analysis.narrow
import tac.Tag
import vc.data.*
import vc.data.TACMeta.SYM_RETURN
import java.math.BigInteger

/**
 * Prepares for the conversion `ReturnCmd`s to `ReturnSymCmd` in [code] for the very simple case of a single primitive returned value,
 * where the returndata is copied from the free memory pointer used in the very last block.
 * The SYM_RETURN meta will be used to replace the return command after inlining.
 * The return commands should be preserved until call graph building since addresses and bounds are resolved there.
 */
fun returnSymbol(code: CoreTACProgram): CoreTACProgram {
    val graph = code.analysisCache.graph
    val mut = code.toPatchingProgram()
    val simplifier = ExpressionSimplifier(graph, graph.cache.def)
    val plusZeroPattern = PatternMatcher.compilePattern(graph, PatternDSL.build {
        (Const(BigInteger.ZERO) + Var { v, w ->
            if (v == TACKeyword.MEM64.toVar()) {
                PatternMatcher.VariableMatch.Match(w)
            } else {
                PatternMatcher.VariableMatch.Continue
            }
        }).commute.withAction { _, _ -> true }
    })

    fun isM0x40(v: TACSymbol, ptr: CmdPointer): Boolean {
        return v is TACSymbol.Var
                && (
                TACKeyword.MEM64.toVar() in code.analysisCache.gvn.equivBefore(ptr, v)
                        || plusZeroPattern.query(v, graph.elab(ptr)).toNullableResult() == true
                )
    }
    // not a good match for DefaultTACCmdMapperWithPointer because we update for each sink in two pointers, and need reference to the mutable TAC program
    graph.sinks.forEach { sink ->
        if (sink.cmd is TACCmd.Simple.ReturnCmd) {
            // is offset tacM0x40?
            val offsetExpected = isM0x40(sink.cmd.o1, sink.ptr)
            val sizeExpected = simplifier.simplify(sink.cmd.o2, sink.ptr, false).equivSym(BigInteger.valueOf(32).asTACSymbol())
            val singleStore =
                graph.elab(sink.ptr.block).commands.filter { it.cmd is TACCmd.Simple.AssigningCmd.ByteStore }
                    .singleOrNull()?.narrow<TACCmd.Simple.AssigningCmd.ByteStore>()
            val singleStoreIsFor0x40 = singleStore?.let {
                isM0x40(it.cmd.loc, it.ptr)
            } ?: false
            if (offsetExpected && sizeExpected && singleStore != null && singleStoreIsFor0x40) {
                val tag = singleStore.cmd.value.tag
                val retSym = TACKeyword.TMP(Tag.Bit256, "retSym")
                mut.addVarDecl(retSym)
                mut.addBefore(singleStore.ptr, listOf(
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(retSym,
                        if (tag == Tag.Bool) {
                            TACExpr.TernaryExp.Ite(
                                singleStore.cmd.value.asSym(),
                                TACSymbol.lift(1).asSym(),
                                TACSymbol.lift(0).asSym()
                            )
                        } else {
                            singleStore.cmd.value.asSym()
                        }
                    )
                ))
                mut.update(sink.ptr) { it.plusMeta(SYM_RETURN,retSym) }
            }
        }
    }

    return mut.toCode(code)
}

/**
 * materialize SYM_RETURN metas
 */
fun materializeReturnSymbol(code: CoreTACProgram): CoreTACProgram {
    val graph = code.analysisCache.graph
    val mut = code.toPatchingProgram()
    graph.commands.forEach { lcmd ->
        if (SYM_RETURN in lcmd.cmd.meta) {
            when (lcmd.cmd) {
                is TACCmd.Simple.ReturnCmd -> {
                    val retSym = lcmd.cmd.meta.find(SYM_RETURN)!!
                    mut.update(lcmd.ptr) { TACCmd.Simple.ReturnSymCmd(retSym,lcmd.cmd.meta) }
                }
                else -> {}
            }
        }
    }

    return mut.toCode(code)
}
