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

package wasm.host.soroban

import analysis.CommandWithRequiredDecls
import vc.data.*

internal abstract class ModuleImpl {
    abstract fun getFuncImpl(
        funcName: String,
        args: List<TACSymbol>,
        retVar: TACSymbol.Var?
    ): CommandWithRequiredDecls<TACCmd.Simple>?

    /** Empty function implementation for summarizing functions with no visible effects (logging, etc.) */
    protected fun noVisibleEffect() = CommandWithRequiredDecls<TACCmd.Simple>()
}
