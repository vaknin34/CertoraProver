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

package analysis.pta

import analysis.CmdPointer
import com.certora.collect.*
import utils.hashObject
import vc.data.TACSymbol
import java.math.BigInteger

object TrivialPointsToInformation : IPointsToInformation {
    private val trivialPointsToSet : WritablePointsToSet = object : WritablePointsToSet, PTANode {
        override fun hashCode() = hashObject(this)

        override fun mayAlias(v: IPointsToSet): Boolean {
            return true
        }

        override fun mustAlias(v: IPointsToSet): Boolean {
            return false
        }

        override fun strongestUpdate() = WritablePointsToSet.UpdateType.WEAK

        override val nodes: Set<PTANode> = setOf(this)
        override val type: IPointsToSet.Type
            get() = IPointsToSet.Type.UNKNOWN


    }

    override fun fieldNodesAt(where: CmdPointer, v: TACSymbol.Var): WritablePointsToSet = trivialPointsToSet
    override fun fieldNodesAt(where: CmdPointer, v: IPointsToSet, offset: BigInteger): WritablePointsToSet {
        return trivialPointsToSet
    }
    override fun fieldNodesAt(where: CmdPointer, c: TACSymbol.Const): WritablePointsToSet = trivialPointsToSet
    override fun fieldNodesAt(where: CmdPointer, s: TACSymbol): WritablePointsToSet = trivialPointsToSet

    override fun contentsOf(where: CmdPointer, set: WritablePointsToSet): IPointsToSet = trivialPointsToSet
    override fun reachableObjects(where: CmdPointer, v: TACSymbol.Var): IPointsToSet = trivialPointsToSet
    override fun reachableObjects(where: CmdPointer, v: IPointsToSet, offset: BigInteger): IPointsToSet = trivialPointsToSet
    override fun arrayFieldAt(where: CmdPointer, v: IPointsToSet): WritablePointsToSet {
        return trivialPointsToSet
    }

    override fun reachableArrayElements(where: CmdPointer, v: IPointsToSet): IPointsToSet = trivialPointsToSet


    override fun <T> query(q: PointsToQuery<T>): T? = null
    override fun lengthFieldAt(where: CmdPointer, set: IPointsToSet): IPointsToSet = trivialPointsToSet

    override val isCompleteSuccess get() = false
}
