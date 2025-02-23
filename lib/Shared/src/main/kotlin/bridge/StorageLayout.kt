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

import kotlinx.serialization.Serializable
import spec.CVLWarningLogger
import tac.TACStorageLayout
import tac.TACStorageSlot
import datastructures.stdcollections.*

@RequiresOptIn
annotation class StorageTestOnly

/**
 * This provides a representation for the JSON format produced by solc for the storageLayout of a contract
 * @types nullable because sometimes input to this will be null (if there are no variables in storage)
 */
@Serializable
data class StorageLayout(val storage: List<StorageSlot>, @property:StorageTestOnly val types: Map<String, SolcType>?, val storageHashArgsReversed: Boolean = false) {
    constructor() : this(listOf(), null)

    @OptIn(StorageTestOnly::class)
    fun toTACStorageLayout(): TACStorageLayout = TACStorageLayout(storageHashArgsReversed, storage.associate { slot ->
        if (slot.descriptor == null) {
            CVLWarningLogger.generalWarning(
                "no type description for slot: $slot"
            )
        }
        slot.label to TACStorageSlot(slot, types)
    })
}
