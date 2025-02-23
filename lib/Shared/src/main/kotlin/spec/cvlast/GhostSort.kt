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

package spec.cvlast

import com.certora.collect.*
import utils.AmbiSerializable
import utils.KSerializable
import utils.hashObject

@KSerializable
@Treapable
sealed class GhostSort : AmbiSerializable {
    @KSerializable
    object Mapping : GhostSort() {
        private fun readResolve(): Any = Mapping
        override fun hashCode() = hashObject(this)
    }

    @KSerializable
    object Function : GhostSort() {
        private fun readResolve(): Any = Function
        override fun hashCode() = hashObject(this)
    }

    @KSerializable
    object Variable : GhostSort() {
        private fun readResolve(): Any = Variable
        override fun hashCode() = hashObject(this)
    }

}
