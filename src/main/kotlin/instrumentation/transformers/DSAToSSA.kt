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

package instrumentation.transformers

import analysis.LTACCmdView
import analysis.narrow
import datastructures.stdcollections.*
import tac.MetaMap
import tac.NBId
import tac.Tag
import utils.parallelStream
import vc.data.*
import vc.gen.LeinoWP
import java.util.stream.Collectors

/**
 * Performs partial SSA-ing - for maps only (Word,Byte,Ghost)
 */
object DSAToSSA {
    fun rewrite(p: CoreTACProgram): CoreTACProgram {
        val c = Collectors.mapping({ it: Pair<TACSymbol.Var, LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>> -> it.second }, Collectors.toList())
        val multiMapWrites = p.analysisCache.graph.commands.parallelStream().filter {
            it.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd &&
                    (it.cmd.lhs.tag == Tag.WordMap || it.cmd.lhs.tag == Tag.ByteMap || it.cmd.lhs.tag is Tag.GhostMap)
        }.map {
            it.narrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()
        }.map {
            it.cmd.lhs to it
        }.collect(Collectors.groupingBy({ it.first }, c)).filterValues {
            it.size > 1
        }
        val mut = p.toPatchingProgram()
        val blockPrefix = mutableMapOf<NBId, MutableList<TACCmd.Simple.AssigningCmd>>()
        multiMapWrites.forEach { (v, writes) ->
            val writeSucc = writes.flatMap {
                p.analysisCache.graph.succ(it.ptr.block)
            }.toSet()
            check(writes.map { it.ptr.block }.let {
                it.toSet().size == it.size
            })
            check(writeSucc.size == 1)
            val succ = writeSucc.first()
            val defaultValueInitCmds = mutableListOf<TACCmd.Simple.AssigningCmd>()
            val forms = writes.map {
                val reachability = LeinoWP.genReachabilityVar(it.ptr.block)
                mut.addVarDecl(reachability)
                defaultValueInitCmds.add(TACCmd.Simple.AssigningCmd.AssignHavocCmd(
                    lhs = reachability
                ))
                reachability to it.cmd.rhs
            }
            check(forms.size > 1)
            val start = forms.first().second
            val iteForm = forms.subList(1, forms.size).fold(start) { Curr, (r, e) ->
                TACExpr.TernaryExp.Ite(
                    i = r.asSym(),
                    t = e,
                    e = Curr
                )
            }
            for(w in writes) {
                mut.replaceCommand(w.ptr, listOf())
            }
            blockPrefix.computeIfAbsent(succ) {
                mutableListOf()
            }.addAll(defaultValueInitCmds +
                    TACCmd.Simple.AssigningCmd.AssignExpCmd(
                        lhs = v,
                        rhs = iteForm,
                        meta = MetaMap()
                    )
            )
        }
        for((b, code) in blockPrefix) {
            val firstPointer = p.analysisCache.graph.elab(b).commands.first().ptr
            mut.addBefore(firstPointer, code)
        }
        return mut.toCode(p)
    }
}