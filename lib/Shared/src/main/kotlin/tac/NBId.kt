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

package tac


import allocator.Allocator
import com.certora.collect.*
import utils.*
import java.util.*

typealias CallId = Int

interface IBlockId { // opaque block ID type
    fun getCallId(): CallId
}

/**
 * [BlockIdentifier], or as it's more commonly referred to, [NBId], is an object for holding identifiers of TAC
 * basic blocks. Its main purpose is to provide unique identification of blocks.
 * In almost all stages of the pipeline, we can consider those identifiers opaque.
 * We usually do not need, nor is it desirable, to consider the fields of this class for semantic reasoning on the code.
 * However, the various fields are sometimes good mnemonics for the source of the code we are analyzing, if we know how
 * those fields values were generated.
 * The main exception to opacity in this class is [calleeIdx]. It is used extensively by both the Inliner, the
 * CVLCompiler and the graph HTML drawer.
 *
 * Below is a detailed explanation about the various fields:
 * [origStartPc] - from the decompiler. indicates the original PC (program counter) value of the command that starts
 *                  this block. Also used by the CVLCompiler but with incrementing opaque values.
 * [stkTop] - from the decompiler. indicates the distance from the max top element of the stack at the start of the
 *              basic block.
 * [decompCopy] - from the decompiler. used by the decompiler to disambiguate entries to the same PC at the same stack
 *                  height with different future jump targets.
 * [calleeIdx] - from the inliner or the CVLCompiler, or any other component capable of combining two TACs together to
 *                  represent distinct VM calls. Used to mark a different TAC code, and the number is also used in
 *                  renaming its local variables (until next phase of DSA/SSA).
 *                  One more use case for [calleeIdx] is in [generateCodeMap()] function, that uses the field to split
 *                  different graph components so that GraphViz is less likely to fail.
 *                  For CVLCompiler generated blocks (CVL Code), it will always by 0. Calls to Solidity from CVL
 *                  will take a TAC of a solidity contract with calleeIdx 0, and update it accordingly there when
 *                  inlining it.
 * [topOfStackValue] - from the decompiler. Used to indicate whether the value at the top of the stack, if interpretable
 *                      as a boolean, is true or false. See interpEdge in Decompiler.kt. It helps resolve additional
 *                      kinds of context-sensitive paths to blocks.
 * [freshCopy] - a general purpose field for differentiating newly generated basic blocks in all parts of the pipeline
 *                  that are not CVLCompiler, Inliner, or Decompiler. It contains no particular meaning.
 *
 *
 * Please note:
 *        *  [Allocator.Id.PC_FOR_NBID] is used to define new block identifiers in [Allocator.getNBId]
 *  In these cases - [stkTop] is guaranteed to be 0
 *
 *  the decompiler creates [NBId] using [EVMPC], for example
 *  ```
 *  TACCmd.Simple.JumpdestCmd(
 *      StartBlock.copy(origStartPc = pc, stkTop = block.stkTop, topOfStackValue = block.topOfStackValue)
 *  )
 * ```
 *
 * So eventhub there can be an overlap between the two [origStartPc] definition methods,
 * [BlockIdentifier] definition is mutually exclusive
 */
@KSerializable
class BlockIdentifier(
    override val origStartPc: Int,
    override val stkTop: Int,
    override val decompCopy: Int,
    override val calleeIdx: CallId,
    // topOfStackValue is repurposed as the inferred value of the top of the stack
    // 1 is true, 2 is false, 0/everything else is anything
    override val topOfStackValue: Int,
    override val freshCopy: Int,
) : NBId() {
    override fun toString(): String {
        return "${origStartPc}_${stkTop}_${decompCopy}_${calleeIdx}_${topOfStackValue}_${freshCopy}"
    }

    fun toCanon(
        idMapper: (Allocator.Id, Int) -> Int,
    ) = CanonBlockIdentifier(
        origStartPc = mapNonDecompiledPc { idMapper(Allocator.Id.PC_FOR_NBID, it) },
        stkTop = stkTop,
        decompCopy = decompCopy,
        calleeIdx = idMapper(Allocator.Id.CALL_ID, calleeIdx),
        topOfStackValue = topOfStackValue,
        freshCopy = idMapper(Allocator.Id.BLOCK_FRESH_COPY, freshCopy),
    )

    // We hash BlockIdentifier a *lot*.  It's worth it to inflate our heap usage just a bit, to speed up
    // hashCode.
    private val cachedHashCode = super.hashCode()
    override fun hashCode() = cachedHashCode

    companion object {
        fun fromCanon(
            canon: CanonBlockIdentifier,
            idMapper: (Int) -> Int,
        ) = BlockIdentifier(
            origStartPc = canon.mapNonDecompiledPc(idMapper),
            stkTop = canon.stkTop,
            decompCopy = idMapper(canon.decompCopy),
            calleeIdx = idMapper(canon.calleeIdx),
            topOfStackValue = canon.topOfStackValue,
            freshCopy = idMapper(canon.freshCopy),
        )


        const val NUM_ELEMENTS = 6 // TODO: Must be updated if number of fields changes
        private const val NUM_ELEMENTS_DEPRECATED = 8 // Keeping for backward compatibility of parseString (used by some unit-tests when parsing .tac files)

        fun parseComponents(elements: List<String>): BlockIdentifier? {
            val origStartPc = elements.getOrNull(0)?.toIntOrNull() ?: return null
            val stkTop = elements.getOrNull(1)?.toIntOrNull() ?: return null
            val decompCopy = elements.getOrNull(2)?.toIntOrNull() ?: return null
            val skip = when (elements.size) {
                NUM_ELEMENTS -> 0
                NUM_ELEMENTS_DEPRECATED -> 1
                else -> return null
            }
            val calleeIdx = elements.getOrNull(3 + skip)?.toIntOrNull() ?: return null
            val topOfStackValue = elements.getOrNull(4 + skip)?.toIntOrNull() ?: return null
            val freshCopy = elements.getOrNull(5 + skip)?.toIntOrNull() ?: return null
            return BlockIdentifier(
                origStartPc = origStartPc,
                stkTop = stkTop,
                decompCopy = decompCopy,
                calleeIdx = calleeIdx,
                topOfStackValue = topOfStackValue,
                freshCopy = freshCopy,
            )
        }

    }
}

@KSerializable
class CanonBlockIdentifier(
    override val origStartPc: Int,
    override val stkTop: Int,
    override val decompCopy: Int,
    override val calleeIdx: CallId,
    override val topOfStackValue: Int,
    override val freshCopy: Int,
) : NBId() {
    override fun toString(): String {
        return "${PREFIX}_${origStartPc}_${stkTop}_${decompCopy}_${calleeIdx}_${topOfStackValue}_${freshCopy}"
    }

    companion object {
        const val PREFIX = "CANONBLOCK"

        fun parseComponents(elements: List<String>): CanonBlockIdentifier? {
            elements.getOrNull(0)?.takeIf { it == PREFIX } ?: return null
            return CanonBlockIdentifier(
                origStartPc = elements.getOrNull(1)?.toIntOrNull() ?: return null,
                stkTop = elements.getOrNull(2)?.toIntOrNull() ?: return null,
                decompCopy = elements.getOrNull(3)?.toIntOrNull() ?: return null,
                calleeIdx = elements.getOrNull(4)?.toIntOrNull() ?: return null,
                topOfStackValue = elements.getOrNull(5)?.toIntOrNull() ?: return null,
                freshCopy = elements.getOrNull(6)?.toIntOrNull() ?: return null,
            )

        }
    }
}
val StartBlock = BlockIdentifier(0, 0, 0, 0, 0, 0)

@KSerializable
@Treapable
sealed class NBId : Comparable<NBId>, IBlockId, AmbiSerializable {
    abstract val origStartPc: Int
    abstract val stkTop: Int
    abstract val decompCopy: Int
    abstract val calleeIdx: CallId

    // topOfStackValue is repurposed as the inferred value of the top of the stack
    // 1 is true, 2 is false, 0/everything else is anything
    abstract val topOfStackValue: Int
    abstract val freshCopy: Int

    override fun getCallId() = calleeIdx

    override fun hashCode(): Int = hash {
        it + origStartPc + stkTop + decompCopy + calleeIdx + topOfStackValue + freshCopy + this::class
    }

    override fun equals(other: Any?): Boolean = if (other is NBId) {
        compareTo(other) == 0
    } else {
        false
    }

    fun fromDecompiler() = stkTop != 0

    fun mapNonDecompiledPc(pcMapper: (Int) -> Int) = if (fromDecompiler()) {
        origStartPc
    } else {
        pcMapper(origStartPc)
    }

    override fun compareTo(other: NBId): Int = when {
        this is BlockIdentifier && other is CanonBlockIdentifier -> 1
        this is CanonBlockIdentifier && other is BlockIdentifier -> -1
        // Yes, there are more concise expressions of this.  But we compare NBId's so much that this is worth it for
        // the speed.
        this.origStartPc < other.origStartPc -> -1
        this.origStartPc > other.origStartPc -> 1
        this.stkTop < other.stkTop -> -1
        this.stkTop > other.stkTop -> 1
        this.decompCopy < other.decompCopy -> -1
        this.decompCopy > other.decompCopy -> 1
        this.calleeIdx < other.calleeIdx -> -1
        this.calleeIdx > other.calleeIdx -> 1
        this.topOfStackValue < other.topOfStackValue -> -1
        this.topOfStackValue > other.topOfStackValue -> 1
        this.freshCopy < other.freshCopy -> -1
        this.freshCopy > other.freshCopy -> 1
        else -> 0
    }

    fun copy(
        origStartPc: Int = this.origStartPc,
        stkTop: Int = this.stkTop,
        decompCopy: Int = this.decompCopy,
        calleeIdx: CallId = this.calleeIdx,
        topOfStackValue: Int = this.topOfStackValue,
        freshCopy: Int = this.freshCopy,
    ): NBId = when (this) {
        is BlockIdentifier -> BlockIdentifier(
            origStartPc = origStartPc,
            stkTop = stkTop,
            decompCopy = decompCopy,
            calleeIdx = calleeIdx,
            topOfStackValue = topOfStackValue,
            freshCopy = freshCopy,
        )
        is CanonBlockIdentifier -> CanonBlockIdentifier(
            origStartPc = origStartPc,
            stkTop = stkTop,
            decompCopy = decompCopy,
            calleeIdx = calleeIdx,
            topOfStackValue = topOfStackValue,
            freshCopy = freshCopy,
        )
    }

    companion object {
        const val ROOT_CALL_ID : CallId = 0

        @Suppress("ForbiddenMethodCall") // ok to `split` - this is a parsing function!
        fun parseString(s: String): NBId = s.split("_").let { elements ->
            if (elements.firstOrNull() == CanonBlockIdentifier.PREFIX) {
                CanonBlockIdentifier.parseComponents(elements)
            } else {
                BlockIdentifier.parseComponents(elements)
            }
        } ?: error("Got invalid block identifier string $s")
    }
}


/**
 * A small utility class from marking two nodes [NBId] that form an edge in a graph as in TAC programs.
 */
data class Edge(val src : NBId, val trg : NBId) {
    override fun toString(): String {
        return "< $src --> $trg >"
    }
}
