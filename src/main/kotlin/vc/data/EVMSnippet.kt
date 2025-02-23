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

import analysis.storage.DisplayPath
import spec.cvlast.CVLType
import java.math.BigInteger

/**
 * These commands can be seen as "debug information" that is attached to TAC programs.
 * These commands are wrapped by annotation commands, so they will not be folded/disappear
 * during transformations/optimizations on the TAC program.
 * These commands should be used to build the CallTrace.
 */
sealed class EVMSnippetCmd : TransformableVarEntityWithSupport<EVMSnippetCmd> {

    /**
     * These commands represent storage accesses done in the Solidity code.
     */
    sealed class StorageSnippet : EVMSnippetCmd() {
        /**
         * Storage access path which will be displayed in the CallTrace.
         */
        abstract val displayPath: DisplayPath

        /**
         * Symbol of the read/written variable.
         */
        abstract val value: TACSymbol

        /**
         * Type of the storage field been accessed.
         */
        abstract val storageType: CVLType.VM?

        /**
         * Address of the contract whose storage is being accessed.
         */
        abstract val contractAddress: BigInteger

        override val support: Set<TACSymbol.Var>
            get() = displayPath.support + ((value as? TACSymbol.Var)?.let { setOf(it) } ?: emptySet())

        protected abstract fun copy(v: TACSymbol, disPath: DisplayPath): StorageSnippet

        override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): EVMSnippetCmd {
            return copy(
                v = (value as? TACSymbol.Var)?.let {
                    f(it)
                } ?: value,
                disPath = displayPath.transformSymbols {
                    if (it is TACSymbol.Var) {
                        f(it)
                    } else {
                        it
                    }
                })
        }

        data class LoadSnippet(
            override val value: TACSymbol,
            override val displayPath: DisplayPath,
            override val storageType: CVLType.VM?,
            override val contractAddress: BigInteger
        ) : StorageSnippet() {
            override fun copy(v: TACSymbol, disPath: DisplayPath): StorageSnippet {
                return copy(value = v, displayPath = disPath)
            }
        }

        data class StoreSnippet(
            override val value: TACSymbol,
            override val displayPath: DisplayPath,
            override val storageType: CVLType.VM?,
            override val contractAddress: BigInteger
        ) : StorageSnippet() {
            override fun copy(v: TACSymbol, disPath: DisplayPath): StorageSnippet {
                return copy(value = v, displayPath = disPath)
            }
        }
    }
}

