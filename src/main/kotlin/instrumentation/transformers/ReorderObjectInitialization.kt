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

import analysis.maybeNarrow
import tac.MetaKey
import utils.mapNotNull
import vc.data.*
import vc.data.SimplePatchingProgram.Companion.patchForEach
import java.math.BigInteger

object ReorderObjectInitialization {

    val FENCE = MetaKey.Nothing("init.reorder.fence")

    fun reorderingFenceInstrumentation(c: CoreTACProgram) : CoreTACProgram {
        return c.parallelLtacStream().mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd.ByteStore>()?.takeIf { store ->
                store.cmd.base == TACKeyword.MEMORY.toVar() &&
                    store.cmd.loc is TACSymbol.Var &&
                    store.cmd.value is TACSymbol.Const &&
                    c.analysisCache.def.defSitesOf(store.cmd.loc as TACSymbol.Var, store.ptr).singleOrNull()?.takeIf {
                        it.block == store.ptr.block
                    }?.let(c.analysisCache.graph::elab)?.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.takeIf {
                        it.cmd.rhs == TACKeyword.MEM64.toVar().asSym()
                    }?.let {
                        c.analysisCache.graph.iterateBlock(start = it.ptr, end = store.ptr.pos, excludeStart = true).none {
                            it.cmd.getLhs() == TACKeyword.MEM64.toVar()
                        }
                    } == true
            }
        }.patchForEach(c) {
            this.addBefore(it.ptr, listOf(TACCmd.Simple.AnnotationCmd(
                FENCE
            )))
        }
    }

    private data class Info(val base: Int?, val offset: BigInteger?, val pos: Int)

    private fun mkRegMap(cs: List<TACCmd.Simple>): Map<TACSymbol.Var, Info> {
        val map = mutableMapOf<TACSymbol.Var, Info>()
        var unknown = 0
        var pos = 0
        for (c in cs) {
            if (c is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
                val assgnLhs = c.lhs
                when (val assgnRhs = c.rhs) {
                    is TACExpr.Sym.Var -> {
                        map[assgnLhs] = Info(unknown, BigInteger.ZERO, pos)
                        unknown += 1
                        pos += 1
                    }
                    is TACExpr.Vec.Add -> {
                        if (assgnRhs.ls.size == 2) {
                            val o1 = assgnRhs.o1
                            val o2 = assgnRhs.o2
                            if (o1 is TACExpr.Sym.Var && o2 is TACExpr.Sym.Const) {
                                map[assgnLhs] =
                                    Info(
                                        map[o1.s]?.base,
                                        map[o1.s]?.offset?.add(o2.s.value),
                                        pos
                                    )
                                pos += 1
                            }
                            if (o1 is TACExpr.Sym.Const && o2 is TACExpr.Sym.Var) {
                                map[assgnLhs] =
                                    Info(
                                        map[o2.s]?.base,
                                        map[o2.s]?.offset?.add(o1.s.value),
                                        pos
                                    )
                                pos += 1
                            }
                        }
                    }
                    else -> {}
                }
            }
        }
        return map
    }

    private fun sameBase(
        c1: TACCmd.Simple,
        c2: TACCmd.Simple,
        map: Map<TACSymbol.Var, Info>
    ): Boolean {
        if (c1 is TACCmd.Simple.AssigningCmd.ByteStore && c2 is TACCmd.Simple.AssigningCmd.ByteStore) {
            return (c1.loc as? TACSymbol.Var)?.let(map::get)?.base?.equals(
                (c2.loc as? TACSymbol.Var)?.let(map::get)?.base ?: return false
            ) == true
        }
        return false
    }

    private fun isBigger(
        c1: TACCmd.Simple,
        c2: TACCmd.Simple,
        map: Map<TACSymbol.Var, Info>
    ): Boolean {
        if (c1 is TACCmd.Simple.AssigningCmd.ByteStore && c2 is TACCmd.Simple.AssigningCmd.ByteStore) {
            val bigger =
                ((c1.loc as? TACSymbol.Var)?.let(map::get)?.offset ?: return false) > ((c2.loc as? TACSymbol.Var)?.let(
                    map::get
                )?.offset ?: return false)
            return sameBase(c1, c2, map) && bigger
        }
        return false
    }

    private fun seenBefore(
        c1: TACCmd.Simple,
        c2: TACCmd.Simple,
        map: Map<TACSymbol.Var, Info>
    ): Boolean {
        if (c1 is TACCmd.Simple.AssigningCmd.ByteStore && c2 is TACCmd.Simple.AssigningCmd.ByteStore) {
            // if there is another location (key) mapped to the same (base, offset) and which appears earlier in the HashMap
            // works since we are in SSA
            val c2Val = map[(c2.loc as? TACSymbol.Var)] ?: return false
            val seen =
                map.any {
                    (it.value.base == c2Val.base) && (it.value.offset == c2Val.offset) && (it.value.pos < (c2Val.pos))
                }
            return sameBase(c1, c2, map) && seen
        }
        return false
    }

    private fun shouldSwap(
        c1: TACCmd.Simple,
        c2: TACCmd.Simple,
        map: Map<TACSymbol.Var, Info>
    ): Boolean {
        if (c2 is TACCmd.Simple.AssigningCmd && c2.lhs == TACKeyword.MEM64.toVar()) {
            return false
        }
        if (c2 is TACCmd.Simple.AssigningCmd.AssignExpCmd && c2.rhs is TACExpr.Sym.Var && c2.rhs.s == TACKeyword.MEM64.toVar()) {
            return false
        }
        if(c1.maybeAnnotation(FENCE)) {
            return false
        }

        if (c1 is TACCmd.Simple.AssigningCmd.ByteStore && c2 is TACCmd.Simple.AssigningCmd.AssignExpCmd) {
            return (c1.loc as? TACSymbol.Var)?.let(map::get)?.base?.equals(
                (c2.lhs).let(map::get)?.base ?: return false
            ) == true
        }
        if (c1 is TACCmd.Simple.AssigningCmd.ByteStore && c2 is TACCmd.Simple.AssigningCmd.ByteStore) {
            return isBigger(c1, c2, map) && !seenBefore(c1, c2, map)
        }
        return false
    }

    fun rewrite(p: CoreTACProgram): CoreTACProgram {
        val blocks = p.analysisCache.graph.blocks
        val mut = p.toPatchingProgram()
        for (b in blocks) {
            val cs = b.commands.map { it.cmd }.toMutableList()
            if (cs.filterIsInstance<TACCmd.Simple.AssigningCmd.ByteStore>().size < 2) {
                continue
            }
            val map = mkRegMap(cs)
            var changed = true
            while (changed) {
                changed = false
                for (i in 1 until cs.size) {
                    if (shouldSwap(cs[i - 1], cs[i], map)) {
                        val tmp = cs[i - 1]
                        cs[i - 1] = cs[i]
                        cs[i] = tmp
                        changed = true
                    }
                }
            }
            assert(b.commands.size == cs.size)
            for (i in 0 until b.commands.size) {
                mut.replaceCommand(b.commands[i].ptr, listOf(cs[i]))
            }
        }
        return mut.toCode(p)
    }
}
