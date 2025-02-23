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

package analysis.patterns

import analysis.CmdPointer
import analysis.LTACVar
import vc.data.TACSymbol

abstract class InfoKey<K> {
    /** Set to true for commands that were matched with a commutative operator, and its arguments were reversed. */
    data class REVERSED(val ptr : CmdPointer) : InfoKey<Boolean>()

    class VarKey : InfoKey<TACSymbol.Var>()
    class LVarKey : InfoKey<LTACVar>()
    class SymKey : InfoKey<TACSymbol>()
}
