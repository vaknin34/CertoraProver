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

import analysis.CmdPointer
import vc.data.TACSymbol

interface IMustEqualsAnalysis {
    fun equivBefore(cmd: CmdPointer, f: TACSymbol.Var) : Set<TACSymbol.Var>
    fun equivAfter(cmd: CmdPointer, f: TACSymbol.Var) : Set<TACSymbol.Var>
    interface Scope {
        fun TACSymbol.equivOf() : Set<TACSymbol>
        fun TACSymbol.Var.equivOf() : Set<TACSymbol.Var>

        fun TACSymbol.equivOfExcluding(v: TACSymbol.Var) : Set<TACSymbol>
        fun TACSymbol.Var.equivOfExcluding(v: TACSymbol.Var) : Set<TACSymbol.Var>
    }

    class ScopeDefinition(val f: (TACSymbol.Var) -> Set<TACSymbol.Var>?) : Scope {
        override fun TACSymbol.equivOf(): Set<TACSymbol> {
            return if(this is TACSymbol.Const) {
                setOf(this)
            } else {
                (this as TACSymbol.Var).equivOf()
            }
        }

        override fun TACSymbol.Var.equivOf(): Set<TACSymbol.Var> = (f(this)?:setOf(this))

        override fun TACSymbol.equivOfExcluding(v: TACSymbol.Var): Set<TACSymbol> {
            return if(this is TACSymbol.Const) {
                this.equivOf()
            } else {
                (this as TACSymbol.Var).equivOfExcluding(v)
            }
        }

        override fun TACSymbol.Var.equivOfExcluding(v: TACSymbol.Var): Set<TACSymbol.Var> {
            return if(this == v) {
                f(this)?.minus(v) ?: setOf()
            } else {
                f(this)?.minus(v) ?: setOf(this)
            }
        }
    }


    fun <R> withEquivBefore(cmd: CmdPointer, f: Scope.() -> R) : R {
        return ScopeDefinition {
            equivBefore(cmd, it)
        }.f()
    }

    fun <R> withEquivAfter(cmd: CmdPointer, f: Scope.() -> R) : R {
        return ScopeDefinition {
            equivAfter(cmd, it)
        }.f()
    }
}