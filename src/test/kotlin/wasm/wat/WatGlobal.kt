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

package wasm.wat

class WatGlobal<T : WatType> internal constructor(
    type: T,
    val name: String
) : WatExpr<T>(type, "global.get \$$name") {

    override fun toString() = "\$$name"

    context(WatBodyBuilder)
    fun set(value: WatExpr<T>) {
        +value
        +"global.set $this"
    }
}
