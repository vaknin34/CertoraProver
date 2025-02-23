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

import analysis.LTACCmd
import analysis.numeric.IntQualifier
import analysis.numeric.PathInformation
import analysis.pta.abi.DecoderAnalysis
import com.certora.collect.*
import utils.AmbiSerializable
import utils.KSerializable
import vc.data.TACExpr
import vc.data.TACSymbol
import java.math.BigInteger

interface IDecoderAnalysis {
    fun isDecoderLengthRead(loc: TACSymbol, pState: PointsToDomain): Boolean
    fun getElementSize(calldataArrayVar: TACSymbol.Var, decoderState: DecoderAnalysis.State): BigInteger?
    fun step(command: LTACCmd, s_: PointsToDomain): DecoderAnalysis.State
    fun consumePath(
        path: Map<TACSymbol.Var, List<PathInformation<IntQualifier>>>,
        decoderState: DecoderAnalysis.State,
        s: PointsToDomain
    ): DecoderAnalysis.State

    fun collectReferenced(
        decoderState: DecoderAnalysis.State,
        referencedFromLive: MutableSet<TACSymbol.Var>,
        lva: Set<TACSymbol.Var>
    )

    fun startBlock(
        decoderState: DecoderAnalysis.State,
        lva: Set<TACSymbol.Var>,
        referencedFromLive: Set<TACSymbol.Var>
    ): DecoderAnalysis.State

    fun endBlock(decoderState: DecoderAnalysis.State, last: LTACCmd, live: Set<TACSymbol.Var>): DecoderAnalysis.State
    fun consumeLoopSummary(
        decoderState: DecoderAnalysis.State,
        s: PointsToDomain,
        s1: LoopCopyAnalysis.LoopCopySummary
    ): DecoderAnalysis.State

    fun interpolate(
        prev: PointsToDomain,
        next: PointsToDomain,
        summary: Map<TACSymbol.Var, TACExpr>
    ): DecoderAnalysis.State

    fun popAllocation(decoderState: DecoderAnalysis.State, s: PointsToDomain): Pair<DecoderAnalysis.State, DecoderAnalysis.BufferDecodeResult?>
    fun isDynamicOffset(v: TACSymbol.Var, whole: PointsToDomain) : Boolean

    @KSerializable
    @Treapable
    data class DirectCalldataRead(
        val bufferAccessPath: DecoderAnalysis.BufferAccessPath,
    ) : AmbiSerializable

    fun getReferencedPrimitivePath(v: TACSymbol, whole: PointsToDomain) : DirectCalldataRead?
    fun kill(d_: DecoderAnalysis.State, killedBySideEffects: Set<TACSymbol.Var>): DecoderAnalysis.State
}
