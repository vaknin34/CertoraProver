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

@file:kotlinx.serialization.UseSerializers(bridge.BigIntegerDecimalSerializer::class)
package bridge

import bridge.types.SolidityTypeDescription
import kotlinx.serialization.Serializable
import java.math.BigInteger

@Serializable
data class StorageSlot(val label: String, val offset: Int, val slot: BigInteger, @property:StorageTestOnly val type: String, val descriptor: SolidityTypeDescription? = null)
