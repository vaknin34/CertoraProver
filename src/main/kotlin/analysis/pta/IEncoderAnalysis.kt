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
import analysis.LTACCmd
import analysis.pta.abi.EncodeOutput
import analysis.pta.abi.EncoderAnalysis
import analysis.pta.abi.ObjectPath
import analysis.pta.abi.TopLevelValue
import vc.data.TACExpr
import vc.data.TACSymbol

interface IEncoderAnalysis {
    data class EncodeCompletePoint(
        val buffer: WritablePointer,
        val encoded: EncodeOutput
    )

    fun collectReferenced(
        encoderState: EncoderAnalysis.State,
        referencedFromLive: MutableSet<TACSymbol.Var>,
        lva: Set<TACSymbol.Var>
    )

    fun startBlock(
        encoderState: EncoderAnalysis.State,
        lva: Set<TACSymbol.Var>,
        referencedFromLive: Set<TACSymbol.Var>
    ): EncoderAnalysis.State

    fun endBlock(encoderState: EncoderAnalysis.State, last: LTACCmd, live: Set<TACSymbol.Var>): EncoderAnalysis.State
    fun interpolate(
        prev: PointsToDomain,
        next: PointsToDomain,
        summary: Map<TACSymbol.Var, TACExpr>
    ): EncoderAnalysis.State

    fun finalizeBuffer(
        encoderState: EncoderAnalysis.State,
        conv: List<ConversionHints>,
        s: PointsToDomain,
        where: LTACCmd
    ): EncoderAnalysis.State

    fun step(command: LTACCmd, s_: PointsToDomain): EncoderAnalysis.State
    fun join(
        encoderState: EncoderAnalysis.State,
        thisContext: PointsToDomain,
        otherState: EncoderAnalysis.State,
        otherContext: PointsToDomain
    ): EncoderAnalysis.State

    val encodeCompletePoints: Map<CmdPointer, EncodeCompletePoint>

    fun toEncodedValue(topLevelWrite: EncoderAnalysis.TopLevelWrite, whole: PointsToDomain) : TopLevelValue
    fun kill(e_: EncoderAnalysis.State, killedBySideEffects: Set<TACSymbol.Var>): EncoderAnalysis.State

    /**
     * A single top level write can be identified by several different paths, i.e. if we encode
     *   s.t.u
     * where s and t are variables of some struct type, we actually have something like
     *   temp1 = s.t
     *   temp2 = temp1.u
     * so we can name the encoded value as "Field u of Root(temp1)" and also "Field u of (Field t of Root(s))".
     *
     * This function collects the possible such names (paths) along with the associated type of the root of each
     * such path. These pairs are returned in a list that is sorted with the "deepest" (most field accesses)
     * _first_
     *
     * @return a list of root type/object path pairs if it is possible to determine the root types
     */
    fun rootTypes(topLevelWrite: EncoderAnalysis.TopLevelWrite, whole: PointsToDomain): List<Pair<HeapType, ObjectPath>>? = null

    fun consumeLoopSummary(
        encoderState: EncoderAnalysis.State,
        ppNextState: PointsToDomain,
        s: LoopCopyAnalysis.LoopCopySummary,
        finalCmd: LTACCmd
    ): EncoderAnalysis.State
}
