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

package analysis.pta.abi

import java.math.BigInteger

data class StridePath(
        val root: BigInteger,
        val path: List<StrideStep>
) {
    constructor(root: Int, path: List<StrideStep>) : this(root.toBigInteger(), path)
    fun appendLoop(k: BigInteger) : StridePath {
        return this.copy(
                path = this.path + StrideStep.StrideLoop(k)
        )
    }

    fun appendConstStep(k: BigInteger) : StridePath {
        if(k == BigInteger.ZERO) {
            return this
        }
        return this.copy(
                path = this.path + StrideStep.ConstStep(k)
        )
    }

}