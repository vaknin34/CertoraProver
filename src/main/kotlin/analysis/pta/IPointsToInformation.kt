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
import vc.data.TACSymbol
import java.math.BigInteger

/**
 * An abstraction of points to information.
 */
interface IPointsToInformation {
    /**
     * At [where] extract a [WritablePointsToSet] that abstracts the locations that are mutated
     * by an update of the index [v]. For example, if [v] points to the beginning of a struct block, then
     * this function returns a points to set that represents the field of the struct.
     */
    fun fieldNodesAt(where: CmdPointer, v: TACSymbol.Var) : WritablePointsToSet?

    /**
     * At [where] extract a [WritablePointsToSet] that abstracts the locations that are mutated
     * by an update of the address [c]. For example, if [c] points to the beginning of a struct block, then
     * this function returns a points to set that represents the field of the struct.
     */
    fun fieldNodesAt(where: CmdPointer, c: TACSymbol.Const) : WritablePointsToSet?

    /**
     * At [where] extract a [WritablePointsToSet] that abstracts the locations that are mutated
     * by an update of the memory referenced by [s]. For example, if [s] points to the beginning of a struct block, then
     * this function returns a points to set that represents the field of the struct.
     */
    fun fieldNodesAt(where: CmdPointer, s: TACSymbol) : WritablePointsToSet?

    /**
     * Given a writable points to set that summarizes writable location in memory, get a points to set that
     * summarizes the values currently contained in those locations.
     */
    fun contentsOf(where: CmdPointer, set: WritablePointsToSet) : IPointsToSet?

    /**
     * Given a variable [v] that points to a writable location in memory, get the points to set that
     * summarizes the values currently contained in that location when the program is at point [where].
     */
    fun contentsOf(where: CmdPointer, v: TACSymbol.Var) : IPointsToSet? = fieldNodesAt(where, v)?.let {
       contentsOf(where, it)
    }

    /**
     * At point [where], return a points to set summarizing the objects pointed to by [v]. Note that
     * this is different from [fieldNodesAt]. For example, if [v] points to the beginning of a struct block,
     * then [reachableObjects] will return a set summarizing the struct object, where [fieldNodesAt] returns
     * a set that summarizes the first field of that struct. Further, this function returns null for variables
     * that do not point to the beginning of an object, field pointers and element pointers into arrays
     * return null, as they do not point to a single, high level object.
     */
    fun reachableObjects(where: CmdPointer, v: TACSymbol.Var) : IPointsToSet?

    /**
     * Given a points to set [v] at location [where] that summarizes of some structs, get the objects in the
     * field at offset [offset]. This function may crash or return null if [v] doesn't point to structs, or [offset] is not
     * a valid offset for all structs referred to in [v].
     */
    fun reachableObjects(where: CmdPointer, v: IPointsToSet, offset: BigInteger) : IPointsToSet?

    fun fieldNodesAt(where: CmdPointer, v: IPointsToSet, offset: BigInteger) : WritablePointsToSet?
    fun arrayFieldAt(where: CmdPointer, v: IPointsToSet) : WritablePointsToSet?

    /**
     * Given a points to set [v], returns a points to set that summarizes all elements of all arrays summarized
     * by [v] at [where]. This pfunction may crash or return null if [v] doesn't point to arrays.
     */
    fun reachableArrayElements(where: CmdPointer, v: IPointsToSet) : IPointsToSet?

    fun <T> query(q: PointsToQuery<T>): T?
    fun lengthFieldAt(where: CmdPointer, set: IPointsToSet): IPointsToSet?

    val isCompleteSuccess: Boolean
}
