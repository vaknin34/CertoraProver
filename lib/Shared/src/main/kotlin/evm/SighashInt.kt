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

@file:kotlinx.serialization.UseSerializers(utils.BigIntegerSerializer::class)
package evm

import com.certora.collect.*
import utils.*
import java.math.BigInteger

@KSerializable
@Treapable
data class SighashInt(val n: BigInteger) : AmbiSerializable {
    init {
        if (n < BigInteger.ZERO || n > BigInteger.TWO.pow(32)) {
            throw IllegalArgumentException("Sighash is a 32-bit number, got $n")
        }
    }

    override fun toString(): String {
        return "SigHash(${n.toString(16)})"
    }

}
