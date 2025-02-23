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

@file:kotlinx.serialization.UseSerializers(BigIntegerSerializer::class)
package vc.data

import allocator.Allocator
import allocator.GenerateRemapper
import allocator.GeneratedBy
import analysis.icfg.ScratchByteRange
import tac.MetaMap
import utils.*
import java.math.BigInteger

/**
 * Summary of a [vc.data.TACCmd.Simple.CallCore] which invokes a constructor
 */
@GenerateRemapper
@KSerializable
data class CreateSummary(
    override val toVar: TACSymbol,
    override val valueVar: TACSymbol,
    override val gasVar: TACSymbol,
    override val inOffset: TACSymbol,
    override val inSize: TACSymbol,
    override val inBase: TACSymbol,
    override val origCallcore: TACCmd.Simple.CallCore,
    @GeneratedBy(Allocator.Id.CALL_SUMMARIES, source = true)
    override val summaryId: Int,
    /**
     * id of the [vc.data.TACBuiltInFunction.Create] invocation that is being initialized here (that
     * id is associated with the [vc.data.TACBuiltInFunction.Create] via the meta)
     */
    @GeneratedBy(Allocator.Id.CONTRACT_CREATION)
    val createId: Int,
    /**
     * Constructor sig, i.e., the known constant subregions of the bytecode passed to the create command
     */
    val constructorSig: Map<ScratchByteRange, BigInteger>
) : ICallCoreSummary, RemapperEntity<CreateSummary> {
    override val outOffset: TACSymbol
        get() = TACSymbol.lift(0)
    override val outSize: TACSymbol
        get() = TACSymbol.lift(0)
    override val outBase: TACSymbol
        get() = TACKeyword.MEMORY.toVar()

    override val callType: TACCallType
        get() = TACCallType.CREATE

    override val variables: Set<TACSymbol.Var>
        get() = setOfNotNull(
            toVar as? TACSymbol.Var,
            valueVar as? TACSymbol.Var,
            gasVar as? TACSymbol.Var,
            inOffset as? TACSymbol.Var,
            inSize as? TACSymbol.Var,
            inBase as? TACSymbol.Var
        )

    override val annotationDesc: String
        get() = "Initialize created contract at $toVar created with signature $constructorSig"

    override fun transformSymbols(f: (TACSymbol.Var) -> TACSymbol.Var): TACSummary {
        fun TACSymbol.map() = (this as? TACSymbol.Var)?.let(f) ?: this
        return CreateSummary(
            toVar = toVar.map(),
            valueVar = valueVar.map(),
            gasVar = gasVar.map(),
            inOffset = inOffset.map(),
            inSize = inSize.map(),
            inBase = inBase.map(),
            origCallcore = origCallcore.transformSymbols(f) as TACCmd.Simple.CallCore,
            summaryId = summaryId,
            createId = createId,
            constructorSig = constructorSig
        )
    }


    override fun withMeta(f: (MetaMap) -> MetaMap): CreateSummary {
        fun TACSymbol.map() = (this as? TACSymbol.Var)?.withMeta(f) ?: this
        return CreateSummary(
            toVar = toVar.map(),
            valueVar = valueVar.map(),
            gasVar = gasVar.map(),
            inOffset = inOffset.map(),
            inSize = inSize.map(),
            inBase = inBase.map(),
            origCallcore = origCallcore.transformSymbols { it.withMeta(f) }.mapMeta(f) as TACCmd.Simple.CallCore,
            summaryId = summaryId,
            createId = createId,
            constructorSig = constructorSig
        )
    }
}
