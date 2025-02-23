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

package verifier.splits

import report.dumps.CountDifficultOps.Companion.processBlock
import report.dumps.Difficulty
import tac.NBId
import utils.SimplePair
import utils.compareTo
import vc.data.CoreTACProgram


/**
 * Stands for a score of one side of a split. A split is a pair of [SideScore] and it's score would be some function
 * of a Pair of side-scores.
 */
interface SideScore<S : SideScore<S>> : Comparable<SideScore<*>> {
    val blocks: Int
    operator fun plus(other: S): S
    operator fun minus(other: S): S
}

interface SplitScorer<V, S : SideScore<S>> {
    /** The score of one block (in our use case) */
    fun ofOne(v: V): S

    /** used to compare splits, because each split is a pair of [SideScore] */
    fun comparePair(p1: SimplePair<S>, p2: SimplePair<S>): Int
}


/** Used as the score of the root split (which is not a real split) */
data object EmptySideScore : SideScore<EmptySideScore> {
    override val blocks get() = 0
    override fun minus(other: EmptySideScore) = error("Don't add $EmptySideScore scores")
    override fun plus(other: EmptySideScore) = error("Don't sub $EmptySideScore scores")
    override fun compareTo(other: SideScore<*>) = error("shouldn't compare $EmptySideScore scores")
}


/**
 * The score is the number of blocks removed in the split compared to its parent.
 */
data class SizeSideScore(override val blocks: Int) : SideScore<SizeSideScore> {
    override fun compareTo(other: SideScore<*>) =
        blocks.compareTo(other.blocks)

    override fun plus(other: SizeSideScore) =
        SizeSideScore(blocks + other.blocks)

    override fun minus(other: SizeSideScore) =
        SizeSideScore(blocks - other.blocks)
}

/**
 * The score of a split - a pair of [SizeSideScore], is the multiplication of the number of removed
 * blocks in the two sides. That's (a bit of a crude) way of trying to get a balanced split.
 */
object SizeScorer : SplitScorer<NBId, SizeSideScore> {
    override fun ofOne(v: NBId) = SizeSideScore(1)
    private val SimplePair<SizeSideScore>.value
        get() = first.blocks.toLong() * second.blocks.toLong()

    override fun comparePair(p1: SimplePair<SizeSideScore>, p2: SimplePair<SizeSideScore>) =
        p1.value.compareTo(p2.value)
}


/**
 * The score is the number of blocks removed, and the number of non-linear-ops removed. When comparing
 * we care first for non-linear-ops.
 */
data class NLSideScore(override val blocks: Int, val nonLinearOps: Int) : SideScore<NLSideScore> {
    override fun compareTo(other: SideScore<*>) =
        if (other is NLSideScore) {
            if (nonLinearOps == other.nonLinearOps) {
                blocks.compareTo(other.blocks)
            } else {
                nonLinearOps.compareTo(other.nonLinearOps)
            }
        } else {
            error("shouldn't compare ${this.javaClass} scores to ${other.javaClass}")
        }

    override fun plus(other: NLSideScore) =
        NLSideScore(blocks + other.blocks, nonLinearOps + other.nonLinearOps)

    override fun minus(other: NLSideScore) =
        NLSideScore(blocks - other.blocks, nonLinearOps - other.nonLinearOps)
}


/**
 * Compares splits (pairs of [NLSideScore]) in a similar way to [SizeScorer], except it first tries to balance
 * according to the multiplication of non-linear operations removed in the two splits, and among the best of these
 * the multiplication of the number of erased blocks.
 */
class NLScorer(val code: CoreTACProgram) : SplitScorer<NBId, NLSideScore> {
    private val g = code.analysisCache.graph

    override fun ofOne(v: NBId): NLSideScore {
        val stats = processBlock(g.elab(v))
        return NLSideScore(1, stats.getOccurrenceCount { it.difficulty == Difficulty.NonLinearity })
    }

    private val SimplePair<NLSideScore>.value
        get() = Pair(
            first.nonLinearOps.toLong() * second.nonLinearOps.toLong(),
            first.blocks.toLong() * second.blocks.toLong()
        )

    override fun comparePair(p1: SimplePair<NLSideScore>, p2: SimplePair<NLSideScore>) =
        p1.value.compareTo(p2.value)
}

