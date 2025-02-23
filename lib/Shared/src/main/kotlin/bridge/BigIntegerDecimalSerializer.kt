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

package bridge

import kotlinx.serialization.KSerializer
import kotlinx.serialization.descriptors.PrimitiveKind
import kotlinx.serialization.descriptors.PrimitiveSerialDescriptor
import kotlinx.serialization.descriptors.SerialDescriptor
import kotlinx.serialization.encoding.Decoder
import kotlinx.serialization.encoding.Encoder
import java.math.BigInteger

class BigIntegerDecimalSerializer : KSerializer<BigInteger> {
    override val descriptor: SerialDescriptor =
        PrimitiveSerialDescriptor(
            "BigIntSerializer",
            PrimitiveKind.STRING
        )

    override fun deserialize(decoder: Decoder): BigInteger {
        try {
            return BigInteger(decoder.decodeString(), 10)
        } catch (e: NumberFormatException) {
            val problematicJson = try {
                decoder.decodeString()
            } catch (e: Exception) {
                e.message
            }
            val msg = "Expecting a decimal integer, got: " +
                    problematicJson
            throw Exception(msg, e)
        }
    }

    override fun serialize(encoder: Encoder, value: BigInteger) =
        encoder.encodeString(value.toString(10))
}