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

import vc.data.*


/**
 * A tac expr with some extra constructs that will need handling on program or command level.
 *
 * Example usage: manage an expression that represents the hash of the byte map range, which introduces both extra
 *  auxiliary variables on creation and an assume or an assert command.
 *
 * @param exp a TAC expression that we're attaching the other two fields to
 * @param declsToAdd contains auxiliary variables that were newly created for [exp] and will
 *  need to be registered
 * @param cmdsToAdd contains commands that were newly created in relation to [exp] and will need to be inserted to the
 *  program; note that it is assumed that these commands are inserted _before_ the use site of [exp]
 */
data class TACExprWithRequiredCmdsAndDecls<T: TACCmd.Spec>(
    val exp: TACExpr,
    val declsToAdd: Set<TACSymbol.Var>,
    val cmdsToAdd: List<T>,
)
