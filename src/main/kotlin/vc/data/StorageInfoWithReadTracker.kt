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

import tac.IStorageInfo
import java.io.Serializable
import datastructures.stdcollections.*
import tac.DummyStorageInfo
import utils.`impossible!`

/**
 * [storageVariables] is a map from the actual storage variables of the contract (the domain) to the so called
 * "read trackers" for that state, see [instrumentation.StorageReadInstrumenter] for details.
 *
 * Null indicates that read tracking is either not enabled, or the storage variable is not a candidate for read tracking
 * (i.e., it's not a map). It is expected (but not enforced here) that if read tracking is enabled and the instrumentation
 * is run that all word maps in the domain [storageVariables] will have a non-null read tracking counterpart, but this
 * is not enforced in this class.
 */
data class StorageInfoWithReadTracker(val storageVariables: Map<TACSymbol.Var, TACSymbol.Var?>) :
    IStorageInfo, Serializable {

    override fun mergeWith(other: IStorageInfo): IStorageInfo {
        return StorageInfoWithReadTracker(storageVariables + when (other){
            is StorageInfo -> other.withDummyReadTrackers().storageVariables
            is StorageInfoWithReadTracker -> other.storageVariables
            else -> `impossible!`
        })
    }

    companion object {

        fun empty() = StorageInfoWithReadTracker(emptyMap())
    }
}

/**
 * StorageInfo refers to just the variables, with no read tracker associated with them
 */
data class StorageInfo(val storageVariables: Set<TACSymbol.Var>) :
    IStorageInfo, Serializable {
    override fun mergeWith(other: IStorageInfo): IStorageInfo {
        return StorageInfo(storageVariables + (other as StorageInfo).storageVariables)
    }

    fun withDummyReadTrackers() = StorageInfoWithReadTracker(this.storageVariables.associate { it to null })

    companion object {
        fun empty() = StorageInfo(emptySet())
    }
}

fun IStorageInfo.stateVars() = when(this) {
    is StorageInfo -> storageVariables
    is StorageInfoWithReadTracker -> storageVariables.keys
    DummyStorageInfo -> setOf()
    else -> throw UnsupportedOperationException("Unknown storage info instance $this: ${this.javaClass}")
}
