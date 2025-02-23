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

package wasm.host.soroban

import analysis.CommandWithRequiredDecls.Companion.mergeMany
import datastructures.stdcollections.*
import tac.*
import utils.*
import vc.data.*
import wasm.host.soroban.*
import wasm.host.soroban.types.*
import wasm.tacutils.*
import wasm.traps.*

object Contract {
    val address = TACKeyword.SOROBAN_ADDRESS_CURRENT.toVar()

    /** (keyDigest, storageType) -> value */
    val contractData = TACKeyword.SOROBAN_CONTRACT_DATA.toVar()

    /** (keyDigest, storageType) -> exists */
    val contractDataKeyDigests = TACKeyword.SOROBAN_CONTRACT_DATA_KEY_DIGESTS.toVar()

    // Storage type constants
    val STORAGE_TYPE_TEMPORARY = 0.asTACExpr
    val STORAGE_TYPE_PERSISTENT = 1.asTACExpr
    val STORAGE_TYPE_INSTANCE = 2.asTACExpr

    fun init() = mergeMany(
        AddressType.new(address),
        assignHavoc(contractData),
        assignHavoc(contractDataKeyDigests),
    )

    fun getCurrentAddress(dest: TACSymbol.Var) =
        assign(dest) { TACKeyword.SOROBAN_ADDRESS_CURRENT.toVar().asSym() }

    fun putContractData(key: TACSymbol, value: TACSymbol, storageType: TACSymbol) =
        Val.withDigest(key.asSym()) { keyDigest ->
            val fullKey = listOf(keyDigest, storageType.asSym())
            mergeMany(
                assign(contractData) {
                    Store(contractData.asSym(), fullKey, value.asSym())
                },
                assign(contractDataKeyDigests) {
                    Store(contractDataKeyDigests.asSym(), fullKey, true.asTACExpr)
                }
            )
        }

    fun hasContractData(dest: TACSymbol.Var, key: TACSymbol, storageType: TACSymbol) =
        Val.withDigest(key.asSym()) { keyDigest ->
            assign(dest) {
                Select(contractDataKeyDigests.asSym(), keyDigest, storageType.asSym())
            }
        }

    fun getContractData(dest: TACSymbol.Var, key: TACSymbol, storageType: TACSymbol) =
        Val.withDigest(key.asSym()) { keyDigest ->
            mergeMany(
                Trap.assert("Contract data not found") {
                    Select(contractDataKeyDigests.asSym(), keyDigest, storageType.asSym())
                },
                assign(dest) {
                    Select(contractData.asSym(), keyDigest, storageType.asSym())
                }
            )
        }

    fun deleteContractData(key: TACSymbol, storageType: TACSymbol) =
        Val.withDigest(key.asSym()) { keyDigest ->
            val fullKey = listOf(keyDigest, storageType.asSym())
            mergeMany(
                assign(contractDataKeyDigests) {
                    Store(contractDataKeyDigests.asSym(), fullKey, false.asTACExpr)
                }
            )
        }

    fun assertValidStorageType(storageType: TACSymbol, module: String, func: String) =
        mergeMany(
            Trap.assert("Expected %1\$s to be a valid StorageType, in $module/$func", storageType) {
                (storageType.asSym() eq STORAGE_TYPE_TEMPORARY) or
                (storageType.asSym() eq STORAGE_TYPE_PERSISTENT) or
                (storageType.asSym() eq STORAGE_TYPE_INSTANCE)
            }
        )

    fun assumeValidStorageType(storageType: TACSymbol) =
        mergeMany(
            assume {
                (storageType.asSym() eq STORAGE_TYPE_TEMPORARY) or
                (storageType.asSym() eq STORAGE_TYPE_PERSISTENT) or
                (storageType.asSym() eq STORAGE_TYPE_INSTANCE)
            }
        )
}
