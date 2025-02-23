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

package analysis.pta.abi

import analysis.LTACCmd
import analysis.LTACCmdView
import analysis.numeric.*
import analysis.numeric.linear.*
import analysis.pta.PointsToDomain
import com.certora.collect.*
import config.Config
import datastructures.stdcollections.*
import utils.*
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACKeyword
import vc.data.TACSymbol
import vc.data.tacexprutil.TACExprFreeVarsCollector

object LinearInvariantSemantics : AbstractAbstractInterpreter<PointsToDomain, LinearInvariants>() {
    override val statementInterpreter: IStatementInterpreter<LinearInvariants, Any?>
        get() = object : AbstractStatementInterpreter<LinearInvariants, Any?>() {
            override fun forget(
                lhs: TACSymbol.Var,
                toStep: LinearInvariants,
                input: LinearInvariants,
                whole: Any?,
                l: LTACCmd
            ): LinearInvariants = toStep.kill(lhs)

            override fun stepExpression(
                lhs: TACSymbol.Var,
                rhs: TACExpr,
                toStep: LinearInvariants,
                input: LinearInvariants,
                whole: Any?,
                l: LTACCmdView<TACCmd.Simple.AssigningCmd.AssignExpCmd>
            ): LinearInvariants {
                val cmd = l.cmd
                return if (cmd.lhs == TACKeyword.MEM64.toVar() || TACKeyword.MEM64.toVar() in TACExprFreeVarsCollector.getFreeVars(cmd.rhs)) {
                    toStep
                } else {
                    val gen = LinearTerm.lift(cmd.rhs)?.takeIf {
                        it.terms.none { (v, _) ->
                            v is LVar.PVar && v.v == cmd.lhs
                        }
                    }?.let {
                        LinearEquality.build {
                            !cmd.lhs `=` it
                        }
                    }
                    toStep + input.genFor(cmd.lhs, rhs = cmd.rhs) + treapSetOfNotNull(gen)
                }
            }
        }

    override val pathSemantics: IPathSemantics<LinearInvariants, PointsToDomain> = TrivialPathSemantics()

    override fun postStep(stepped: LinearInvariants, l: LTACCmd): LinearInvariants = stepped

    override fun killLHS(
        lhs: TACSymbol.Var,
        s: LinearInvariants,
        w: PointsToDomain,
        narrow: LTACCmdView<TACCmd.Simple.AssigningCmd>
    ): LinearInvariants {
        return s.kill(lhs)
    }

    override fun project(l: LTACCmd, w: PointsToDomain): LinearInvariants {
        return w.invariants
    }

    fun collectReferenced(invariants: LinearInvariants, referencedFromLive: MutableSet<TACSymbol.Var>, lva: Set<TACSymbol.Var>) {
        invariants.forEach {
            if(it.term.any {(k, _) ->
                    k is LVar.PVar && k.v in lva
                }) {
                it.term.mapNotNullTo(referencedFromLive) {
                    (it.key as? LVar.PVar)?.v
                }
            }
        }
    }

    fun endBlock(
        invariants: LinearInvariants,
        last: LTACCmd,
        live: Set<TACSymbol.Var>
    ) : LinearInvariants {
        unused(last)
        unused(live)
        return invariants.updateElements {
            when {
                it.term.size <= Config.LinearInvariantBound.get() -> it.canonicalize()
                else -> null
            }
        }
    }

    fun startBlock(invariants: LinearInvariants, lva: Set<TACSymbol.Var>, referencedFromLive: Set<TACSymbol.Var>): LinearInvariants {
        val vars = lva.toTreapSet() + referencedFromLive.toTreapSet()
        return invariants.retainAll { it.relatesAny(vars) }
    }
}
