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

package vc.data

import com.certora.collect.*
import utils.hash
import utils.KSerializable
import utils.AmbiSerializable

@KSerializable
@Treapable
class UfAxioms(private val underlying: Map<FunctionInScope.UF, List<TACAxiom>>) : AmbiSerializable {
    companion object {
        fun empty() = UfAxioms(mapOf())
    }

    operator fun invoke(k: FunctionInScope.UF) = underlying.get(k)
    operator fun get(k: FunctionInScope.UF) = underlying[k]

    fun <T> mapTo(f: (Map<FunctionInScope.UF, List<TACAxiom>>) -> T) =
        f(underlying)

    fun merge(other: UfAxioms) =
        UfAxioms(
            underlying.entries
                .plus(other.underlying.entries)
                .associate { (uf, axioms) -> uf to axioms }
        )

    override fun hashCode() = hash { it + underlying }
}
