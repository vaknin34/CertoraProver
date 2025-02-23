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

package analysis.storage

import com.certora.collect.*
import datastructures.stdcollections.*
import utils.*
import vc.data.*

@kotlinx.serialization.Serializable
@Treapable
data class DisplayPaths(val paths: Set<DisplayPath>) : TransformableSymEntityWithRlxSupport<DisplayPaths>, AmbiSerializable {

    override fun transformSymbols(f: (TACSymbol) -> TACSymbol): DisplayPaths =
        DisplayPaths(paths.mapTo(mutableSetOf()) {
            it.transformSymbols(f)
        })
}

/**
 * while [DisplayPaths.paths] may, in some corner cases,
 * contain more than one [DisplayPath], we usually don't expect it to
 * nor does most existing code attempt to handle this case.
 *
 * this may change in the future, and if it does, this function should be removed.
 */
fun TACSymbol.singleDisplayPathOrNull(): DisplayPath? {
    return (this as? TACSymbol.Var)
        ?.meta
        ?.find(TACMeta.DISPLAY_PATHS)
        ?.paths
        ?.singleOrNull()
}
