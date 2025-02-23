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

package analysis.dataflow

import analysis.*
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol

typealias MEDomain = Set<TACSymbol.Var>
/*
   Computes definitional equalities at each program point. This class does NOT propagate or handle "semantic"
   or propositional equality. That is, for
   a = 5
   b = 5
   the analysis will not conclude that a == b after the second assignment.
 */
class MustEqualsAnalysis(graph: TACCommandGraph) : TACCommandDataflowAnalysis<Map<TACSymbol.Var, MEDomain>>(
        graph, JoinLattice.ofJoin { a, b ->
    val toFold = b.toMutableMap()
    for ((k, v) in a) {
        if (toFold[k] === v) {
            continue
        } else if (k !in toFold) {
            toFold[k] = setOf(k)
        } else {
            toFold[k] = toFold[k]!!.intersect(v)
            assert(k in toFold[k]!!)
        }
    }
    toFold.toMap()
}, mapOf(), Direction.FORWARD), IMustEqualsAnalysis {
    override fun transformCmd(inState: Map<TACSymbol.Var, MEDomain>, cmd: LTACCmd): Map<TACSymbol.Var, MEDomain> =
        when {
            cmd.cmd is TACCmd.Simple.AssigningCmd.AssignExpCmd && cmd.cmd.rhs is TACExpr.Sym.Var->
                this.saturateOnAssignment(inState, cmd.cmd.lhs, cmd.cmd.rhs.s)
            cmd.cmd is TACCmd.Simple.AssigningCmd ->
                this.kill(inState, cmd.cmd.lhs)
            else -> inState
        }


    private fun Map<TACSymbol.Var, MEDomain>.equivClass(v: TACSymbol.Var) : Set<TACSymbol.Var> {
        return this.getOrDefault(v, setOf(v))
    }

    private fun kill(m: MutableMap<TACSymbol.Var, MEDomain>, v: TACSymbol.Var) {
        val newSet = m.equivClass(v).minus(v)
        for(k in newSet) {
            m[k] = newSet
        }
    }

    fun kill(m: Map<TACSymbol.Var, MEDomain>, v: TACSymbol.Var): Map<TACSymbol.Var, MEDomain> =
        m.toMutableMap().let { mut ->
            kill(mut, v)
            mut[v] = setOf(v)
            mut
        }

    /*
    We only need to run one round of saturation at each assignment because we are sure all previous assignments have eagerly
    been saturated. Thus only one round is sufficient as the system is fully saturated except for the change induced by
    the assignemnt
     */
    private fun saturateOnAssignment(m: Map<TACSymbol.Var, MEDomain>, lhs: TACSymbol.Var, rhs: TACSymbol.Var) : Map<TACSymbol.Var, MEDomain> {
        val toUnion = m.equivClass(rhs).plus(lhs)
        val mut = m.toMutableMap()
        kill(mut, lhs)
        for(up in toUnion) {
            mut[up] = toUnion
        }
        return mut
    }

    init {
        runAnalysis()
    }

    private fun <R> runEquiv(map: Map<TACSymbol.Var, MEDomain>?, f: IMustEqualsAnalysis.Scope.() -> R) : R {
        if(map == null) {
            return (object: IMustEqualsAnalysis.Scope {
                override fun TACSymbol.equivOf(): Set<TACSymbol> =
                    setOf(this)

                override fun TACSymbol.Var.equivOf(): Set<TACSymbol.Var> =
                    setOf(this)

                override fun TACSymbol.equivOfExcluding(v: TACSymbol.Var): Set<TACSymbol> {
                    return if(v == this) {
                        setOf()
                    } else {
                        setOf(this)
                    }
                }

                override fun TACSymbol.Var.equivOfExcluding(v: TACSymbol.Var): Set<TACSymbol.Var> {
                    return if(v == this) {
                        setOf()
                    } else {
                        setOf(this)
                    }
                }

            }).f()
        }
        return IMustEqualsAnalysis.ScopeDefinition(map::get).f()
    }

    override fun <R> withEquivBefore(cmd: CmdPointer, f: IMustEqualsAnalysis.Scope.() -> R) : R {
        return runEquiv(cmdIn[cmd], f)
    }

    override fun <R> withEquivAfter(cmd: CmdPointer, f: IMustEqualsAnalysis.Scope.() -> R) : R {
        return runEquiv(cmdOut[cmd], f)
    }

    override fun equivAfter(cmd: CmdPointer, f: TACSymbol.Var): Set<TACSymbol.Var> =
        cmdOut[cmd]?.equivClass(f) ?: setOf(f)

    override fun equivBefore(cmd: CmdPointer, f: TACSymbol.Var) : Set<TACSymbol.Var> = cmdIn[cmd]?.equivClass(f) ?: setOf(f)
}
