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

package analysis

import analysis.worklist.SimpleWorklist
import datastructures.stdcollections.*
import log.Logger
import log.LoggerTypes
import utils.`to?`
import utils.mapNotNull
import utils.monadicMap
import utils.parallelStream
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACKeyword
import vc.data.TACSymbol
import java.math.BigInteger
import java.util.stream.Collectors

private val logger = Logger(LoggerTypes.ALIAS_ANALYSIS)

/**
 * An analysis that tries to prove that every calldata access is either:
 * 1. a constant, or
 * 2. a value *definitely* derived from an addition to a read from calldata
 *
 * The second condition approximates "a dynamic offset later in the calldata buffer", which we assume never overlaps
 * with a constant index. Note that if this assumption is wrong, then we don't become unsound, but imprecise (because
 * the solver is free to invent two different values for two reads that actually alias).
 *
 * The analysis is effected by computing the LFP of a set of equations computed from the def chains for every
 * calldata read. The equations are generated via the following rules:
 *
 * `[[ l:x = calldata(y) ]]` := x@l = Read(y@l)
 * `[[ l:x = y + z ]]` := x@l = Add(y@l ,z@l)
 * `[[ l:x = y + k ]]` := x@l = AddK(y@l, k)
 * `[[ l:x = k ]]= := x@l = k
 * `[[ l:x = expr ]]` := x@l = Other
 *
 *  if a symbol/location pair has multiple possible definitions (due to DSA joins), then we generate:
 *  x@l := y@l' \/ z@l'' \/ ...
 *
 *  For every possible defining symbol.
 *
 *  The abstract semantics of Add, Read, and AddK are as follows:
 *
 *  Add(_, CalldataRead) = CalldataRead
 *  Add(CalldataRead, _) = CallDataRead
 *  Add(k1, k2) = k1 + k2
 *  Add(_, _) = Other
 *
 *  Read(CalldataRead) = CalldataRead
 *  Read(k) = CalldataRead
 *  Read(Other) = Other
 *
 *  AddK(CalldataRead, k) = CalldataRead
 *  AddK(k1, k2) = k1 + k2
 *  AddK(_, k) = Other
 *
 *  The abstract domain is a flat constant lattice, with Other being the supremum, and Kotlin's null being the bottom element.
 *
 *  If all calldata reads are CalldataRead or some value k, then scalarization is safe; if the abstract value for a
 *  read is CalldataRead, then value must be the addition to some value read out of calldata or an offset read out
 *  of calldata immediately, which approximates our desired condition. A more precise anlaysis would require at least one
 *  addition to a calldataread value before it is used again, but this is "good enough" and if we are wrong, we are
 *  introducing only imprecision.
 */
class CalldataAnalysis(
    private val graph: TACCommandGraph
) {
    data class CalldataAccess(val base: TACSymbol.Var, val idx: TACSymbol, val cmd: LTACCmd)
    sealed class AliasResult {
        object Imprecise : AliasResult()
        data class Valid(val accesses: Map<CalldataAccess, BigInteger>) : AliasResult()
    }

    private fun getAccessFromCommand(access: LTACCmd) =
        when (access.cmd) {
            is TACCmd.Simple.AssigningCmd.ByteLoad -> if(access.cmd.base == TACKeyword.CALLDATA.toVar()) {
                CalldataAccess(access.cmd.base, access.cmd.loc, access)
            } else {
                null
            }
            else -> null
        }

    private fun runAnalysis(): AliasResult {
        val mapAccesses = graph.commands.parallelStream().mapNotNull {
            getAccessFromCommand(it)
        }.collect(Collectors.toList())

        val nonTrivialDefAnalysis = NonTrivialDefAnalysis(def = graph.cache.def, graph = graph)
        val eqn = mutableMapOf<Pair<CmdPointer, TACSymbol.Var>, FlowFunction>()
        var failed = false
        SimpleWorklist.iterateWorklist(mapAccesses.mapNotNull {
            it.cmd.ptr `to?` (it.idx as? TACSymbol.Var)
        }) loop@{ it, nxt ->
            if(it in eqn || failed) {
                return@loop
            }
            logger.trace {
                "Visiting $it"
            }
            val defs = nonTrivialDefAnalysis.nontrivialDef(src = it.second, origin = it.first)
            if(defs.isEmpty()) {
                eqn[it] = FlowFunction.Other
                return@loop
            } else if(defs.size == 1) {
                val def = graph.elab(defs.single()).maybeNarrow<TACCmd.Simple.AssigningCmd>() ?: return@loop run { failed = true }
                handleDefinition(def, nxt, eqn, it)
            } else if(defs.size >= 2) {
                val joinOver = defs.monadicMap {
                    graph.elab(it).maybeNarrow<TACCmd.Simple.AssigningCmd>()
                } ?: return@loop run {
                    failed = true
                }

                eqn[it] = FlowFunction.Join(joinOver.map {
                    it.ptr to it.cmd.lhs
                })
                joinOver.forEach {
                    handleDefinition(
                        def = it,
                        nxt = nxt,
                        eqn = eqn,
                        sym = it.ptr to it.cmd.lhs
                    )
                }
            }
        }
        if(failed) {
            logger.warn {
                "Calldata scalarization failed: equation computation failed"
            }
            return AliasResult.Imprecise
        }
        logger.debug {
            "Equation computation complete, starting solver"
        }
        logger.trace {
            "Equation dump $eqn"
        }
        val res = KleeneSolver<Pair<CmdPointer, TACSymbol.Var>, AVal>(AVal.Companion.Lattice).solve(eqn)
        logger.debug {
            "Solving complete"
        }
        val toReturn = mutableMapOf<CalldataAccess, BigInteger>()
        for(m in mapAccesses) {
            if(m.idx is TACSymbol.Const) {
                toReturn[m] = m.idx.value
                continue
            }
            check(m.idx is TACSymbol.Var)
            val k = m.cmd.ptr to m.idx
            val r = res[k] ?: return run {
                logger.warn {
                    "Solver did not produce a result for $k"
                }
                AliasResult.Imprecise
            }
            when(r) {
                AVal.CalldataRead -> Unit
                is AVal.Const -> toReturn[m] = r.k
                AVal.Other -> {
                    logger.warn {
                        "Failed to scalarize calldata read at ${m.cmd}"
                    }
                    dumpSolverTrace(k, eqn, res)
                    return AliasResult.Imprecise
                }
            }
        }
        return AliasResult.Valid(toReturn)
    }

    private fun handleDefinition(
        def: LTACCmdView<TACCmd.Simple.AssigningCmd>,
        nxt: MutableCollection<Pair<CmdPointer, TACSymbol.Var>>,
        eqn: MutableMap<Pair<CmdPointer, TACSymbol.Var>, FlowFunction>,
        sym: Pair<CmdPointer, TACSymbol.Var>
    ) {
        val e = when (val c = def.cmd) {
            is TACCmd.Simple.AssigningCmd.ByteLoad -> {
                if (c.base != TACKeyword.CALLDATA.toVar()) {
                    FlowFunction.Other
                } else if (c.loc is TACSymbol.Const) {
                    FlowFunction.Read
                } else {
                    check(c.loc is TACSymbol.Var)
                    nxt.add(def.ptr to c.loc)
                    FlowFunction.ReadAt(def.ptr to c.loc)
                }
            }
            is TACCmd.Simple.AssigningCmd.AssignExpCmd -> {
                when (c.rhs) {
                    is TACExpr.Sym.Const -> {
                        FlowFunction.K(c.rhs.s.value)
                    }
                    is TACExpr.Sym.Var -> {
                        FlowFunction.Assign(def.ptr to c.rhs.s)
                    }
                    is TACExpr.Vec.Add -> {
                        if (c.rhs.ls.size != 2 || !c.rhs.operandsAreSyms()) {
                            FlowFunction.Other
                        } else {
                            val (k, v) = c.rhs.ls.partition {
                                it is TACExpr.Sym.Const
                            }
                            if (k.size == 2) {
                                FlowFunction.K(k.map { (it as TACExpr.Sym.Const).s.value }.reduce(BigInteger::add))
                            } else if (k.size == 1) {
                                FlowFunction.AddK(
                                    k = (k.single() as TACExpr.Sym.Const).s.value,
                                    o1 = def.ptr to (v.single() as TACExpr.Sym.Var).s
                                )
                            } else {
                                check(v.size == 2)
                                FlowFunction.Add(
                                    o1 = def.ptr to (v[0] as TACExpr.Sym.Var).s,
                                    o2 = def.ptr to (v[1] as TACExpr.Sym.Var).s
                                )
                            }
                        }
                    }
                    else -> FlowFunction.Other
                }
            }
            else -> FlowFunction.Other
        }
        nxt.addAll(e.deps())
        eqn[sym] = e
    }

    private fun dumpSolverTrace(
        k: Pair<CmdPointer, TACSymbol.Var>,
        eqn: Map<Pair<CmdPointer, TACSymbol.Var>, FlowFunction>,
        res: Map<Pair<CmdPointer, TACSymbol.Var>, AVal>
    ) {
        val visited = mutableSetOf<Pair<CmdPointer, TACSymbol.Var>>()
        SimpleWorklist.iterateWorklist(listOf(k)) { p, nxt ->
            if(!visited.add(p)) {
                return@iterateWorklist
            }
            val flowFunction = eqn[p]!!
            logger.debug {
                "$p := ${res[p]}, by $flowFunction"
            }
            nxt.addAll(flowFunction.deps())
        }
    }

    private sealed class AVal {
        object Other: AVal()
        data class Const(val k: BigInteger) : AVal()
        object CalldataRead : AVal()
        companion object {
            object Lattice : JoinLattice<AVal> {
                override fun join(x: AVal, y: AVal): AVal {
                    return if(x == y) {
                        x
                    } else {
                        Other
                    }
                }

                override fun equiv(x: AVal, y: AVal): Boolean {
                    return x == y
                }
            }
        }
    }

    private sealed class FlowFunction : KleeneSolver.SolverFunction<Pair<CmdPointer, TACSymbol.Var>, AVal> {
        open fun deps(): Collection<Pair<CmdPointer, TACSymbol.Var>> = listOf()

        data class Join(val of: List<Pair<CmdPointer, TACSymbol.Var>>) : FlowFunction() {
            override fun eval(st: Map<Pair<CmdPointer, TACSymbol.Var>, AVal>): AVal? {
                return of.mapNotNull {
                    st[it]
                }.reduceOrNull(AVal.Companion.Lattice::join)
            }

            override fun deps(): Collection<Pair<CmdPointer, TACSymbol.Var>> {
                return of
            }
        }

        data class AddK(val o1: Pair<CmdPointer, TACSymbol.Var>, val k : BigInteger) : FlowFunction() {
            override fun eval(st: Map<Pair<CmdPointer, TACSymbol.Var>, AVal>): AVal? {
                return st.get(o1)?.let {
                    when (it) {
                        is AVal.Const -> {
                            AVal.Const(k = it.k + k)
                        }
                        is AVal.CalldataRead -> {
                            it
                        }
                        is AVal.Other -> {
                            it
                        }
                    }
                }
            }

            override fun deps(): Collection<Pair<CmdPointer, TACSymbol.Var>> {
                return listOf(o1)
            }
        }

        data class Add(val o1: Pair<CmdPointer, TACSymbol.Var>, val o2: Pair<CmdPointer, TACSymbol.Var>) : FlowFunction() {
            override fun eval(st: Map<Pair<CmdPointer, TACSymbol.Var>, AVal>): AVal? {
                val v1 = st[o1] ?: return null
                val v2 = st[o2] ?: return null
                return when(v1) {
                    AVal.CalldataRead -> {
                        v1
                    }
                    is AVal.Const -> {
                        if (v2 is AVal.Const) {
                            v1.copy(k = v1.k + v2.k)
                        } else {
                            v2
                        }
                    }
                    AVal.Other -> {
                        if (v2 is AVal.CalldataRead) {
                            v2
                        } else {
                            v1
                        }
                    }
                }
            }

            override fun deps(): Collection<Pair<CmdPointer, TACSymbol.Var>> {
                return listOf(o1, o2)
            }
        }

        data class Assign(val which: Pair<CmdPointer, TACSymbol.Var>) : FlowFunction() {
            override fun eval(st: Map<Pair<CmdPointer, TACSymbol.Var>, AVal>): AVal? {
                return st.get(which)
            }

            override fun deps(): Collection<Pair<CmdPointer, TACSymbol.Var>> {
                return listOf(which)
            }
        }

        object Read : FlowFunction() {
            override fun eval(st: Map<Pair<CmdPointer, TACSymbol.Var>, AVal>): AVal? {
                return AVal.CalldataRead
            }

        }

        object Other : FlowFunction() {
            override fun eval(st: Map<Pair<CmdPointer, TACSymbol.Var>, AVal>): AVal {
                return AVal.Other
            }
        }

        data class ReadAt(val which: Pair<CmdPointer, TACSymbol.Var>) : FlowFunction() {
            override fun eval(st: Map<Pair<CmdPointer, TACSymbol.Var>, AVal>): AVal? {
                return st.get(which)?.let {
                    if(it is AVal.CalldataRead || it is AVal.Const) {
                        AVal.CalldataRead
                    } else {
                        AVal.Other
                    }
                }
            }

            override fun deps(): Collection<Pair<CmdPointer, TACSymbol.Var>> {
                return listOf(which)
            }
        }

        data class K(val k: BigInteger) : FlowFunction() {
            override fun eval(st: Map<Pair<CmdPointer, TACSymbol.Var>, AVal>): AVal {
                return AVal.Const(k)
            }
        }
    }

    val result = runAnalysis()
}
