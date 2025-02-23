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

import vc.data.TACSymbol
import tac.Tag

interface MockStackVarMixin {
    val L1024 get() = TACSymbol.Var("L1024", Tag.Bit256)
    val L1023 get() = TACSymbol.Var("L1023", Tag.Bit256)
    val L1022 get() = TACSymbol.Var("L1022", Tag.Bit256)
    val L1021 get() = TACSymbol.Var("L1021", Tag.Bit256)
    val L1020 get() = TACSymbol.Var("L1020", Tag.Bit256)
}
