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

package analysis.icfg

import tac.MetaMap
import tac.Tag
import vc.data.TACMeta
import vc.data.TACSymbol

object CalldataDeterminismHelper {

    private val naryDeterminism = datastructures.stdcollections.mutableMapOf<Int, TACSymbol.Var>()

    private const val determinismPrefix = "certoraDeterminsic"

    fun deterministicFor(arity: Int) : TACSymbol.Var {
        return naryDeterminism.getOrPut(arity) {
            TACSymbol.Var(
                namePrefix = "$determinismPrefix$arity",
                tag = Tag.GhostMap(
                    paramSorts = List(arity) {
                        Tag.Bit256
                    },
                    resultSort = Tag.Bit256
                ),
                meta = MetaMap(TACMeta.NO_CALLINDEX)
            )
        }
    }
}
