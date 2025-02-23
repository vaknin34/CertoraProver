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

package analysis.pta

import analysis.CmdPointer
import analysis.LTACCmd
import analysis.alloc.AllocationAnalysis
import vc.data.TACSymbol
import java.math.BigInteger

interface SymInterpreter<R, V> {

    fun interpSymbol(where: LTACCmd, st: R, sym: TACSymbol): V {
        return when(sym) {
            is TACSymbol.Const -> if (sym.value == 0x60.toBigInteger()) {
                this.liftAmbiguous(this.typeVariableManager.getVariableForSite(where))
            } else {
                this.liftInt(sym.value)
            }

            is TACSymbol.Var -> {
                val isLHS = (where.cmd.getLhs() == sym)
                if (isLHS && where.ptr in scratchSite) {
                    this.scratch
                } else if (isLHS && where.ptr in allocSites) {
                    this.pointerFor(allocSites[where.ptr]!!)
                } else {
                    st.lookup(sym) ?: untracked
                }
            }
        }
    }

    fun pointerFor(abstractLocation: AllocationAnalysis.AbstractLocation) : V
    fun liftInt(value: BigInteger) : V
    fun liftAmbiguous(variableForSite: TypeVariable) : V

    fun R.lookup(sym: TACSymbol.Var): V?
    fun R.interp(sym: TACSymbol, where: LTACCmd) : V = interpSymbol(where, this, sym)
    fun V.maybeResolve(): V


    val scratch: V
    val untracked : V

    val scratchSite: Set<CmdPointer>
    val allocSites: Map<CmdPointer, AllocationAnalysis.AbstractLocation>
    val typeVariableManager: TypeVariableManager
}
