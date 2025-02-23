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

package vc.gen

import vc.data.LExpression

/**
 * An [LExpression] representing some TAC code block, along with a list of definitions that are used in
 * the lExpression.
 */
data class BlockBody(val blockBody: LExpression, val definitions: List<LExpression>) {

    fun update(newBody: LExpression, definition: LExpression? = null): BlockBody =
        BlockBody(newBody, definitions + listOfNotNull(definition))

    fun map(f: (LExpression) -> LExpression) : BlockBody = BlockBody(f(blockBody), definitions.map(f))

    fun withDefinitions(definitions: List<LExpression>) = BlockBody(blockBody, this.definitions + definitions)
}