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

import com.certora.collect.*
import datastructures.stdcollections.*
import tac.MetaMap
import tac.NBId
import utils.AmbiSerializable
import utils.KSerializable

/**
 * Summary to be used with SummaryCmd. Summarizes some high level behavior in the TAC.
 * Not to be confused with the CVL-level summaries that are determined by the user to summarize
 * high-level code (e.g. calls to Solidity).
 */
interface TACSummary : AmbiSerializable, TransformableVarEntity<TACSummary> {
    /**
     * Variables that are referenced in this summary.
     */
    val variables: Set<TACSymbol.Var>

    /**
     * Human readable description of the summary
     */
    val annotationDesc: String

    fun withMeta(f: (MetaMap) -> MetaMap) = this
}

interface AssigningSummary {
    val mayWriteVars: Collection<TACSymbol.Var>
    val mustWriteVars: Collection<TACSymbol.Var>
}

/**
 * A conditional summary of some set of blocks. This summary encodes some pre-condition that must hold for the summary
 * to apply. The precondition must only reference variables in [variables].
 *
 * If the precondition holds, then analyses may skip directly to [skipTarget], applying whatever summary is
 * represented by this object. If the precondition does not hold, then analyses/translation/etc. should jump
 * to [originalBlockStart], which is the beginning of the summarized code.
 */
interface ConditionalBlockSummary : TACSummary, AssigningSummary {
    /**
     * All the blocks summarized by this summary (assuming the precondition holds). The sole success of [summarizedBlocks] should
     * be [skipTarget], and the containing SummaryCmd should dominate all blocks in [summarizedBlocks]
     */
    val summarizedBlocks: Set<NBId>

    /**
     * The (unique) beginning of the summarized blocks held in [summarizedBlocks]
     */
    val originalBlockStart : NBId

    /**
     * The target to skip to if the precondition holds.
     */
    val skipTarget : NBId

    /**
     * Variables mutated within [summarizedBlocks], to be havoced by analyses when skipping to [skipTarget]
     */
    val modifiedVars: Set<TACSymbol.Var>

    override val mayWriteVars: Collection<TACSymbol.Var>
        get() = modifiedVars

    override val mustWriteVars: Collection<TACSymbol.Var>
        get() = listOf()

    val successors: TreapSet<NBId>
        get() = treapSetOf(originalBlockStart, skipTarget)

    /**
     * Using the partial function [f], generate an equivalent summary modulo the renaming in f. If [f] doesn't
     * return a block _required_ by this summary, this function may throw.
     */
    fun remapBlocks(f: (NBId) -> NBId?) : ConditionalBlockSummary
}

interface IOpcodeSummary {
    val opcode: String
}

@KSerializable
abstract class OpcodeSummary: TACSummary, IOpcodeSummary {
    abstract val hostContract: TACSymbol.Var

    override val annotationDesc: String
        get() = "Opcode summary for $opcode"
}
