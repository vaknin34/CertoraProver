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

package vc.summary

import algorithms.AssociativityRequirement
import analysis.LTACCmd
import vc.data.*

interface ComputeTACSummary<R> {
    val associativityRequirement: AssociativityRequirement

    fun sequentialComposition(vararg sums: R): R = sequentialComposition(sums.toList())

    fun sequentialComposition(rs: List<R>): R

    fun parallelComposition(vararg sums: R): R = parallelComposition(sums.toList())

    fun parallelComposition(rs: List<R>): R


    fun summarizeCmd(cmd: LTACCmd): R = summarizeCmd(
        HasTACCommand.LTACCmd(cmd))
    fun summarizeCmd(cmd: HasTACCommand): R

    fun summarizeLoop(loopBody: R): R

    sealed interface HasTACCommand {
        val cmd: TACCmd.Simple

        @JvmInline
        value class LTACCmd(val ltacCmd: analysis.LTACCmd): HasTACCommand {
            override val cmd: TACCmd.Simple
                get() = ltacCmd.cmd

            override fun toString(): String = ltacCmd.toString()
        }

        class SimpleTACCmd(override val cmd: TACCmd.Simple): HasTACCommand {
            override fun toString(): String = cmd.toString()
        }
    }
}

interface TACSummaryWithTransFormula : TACSummary {
    val transFormula: TACTransFormula

    fun copy(
        newTransFormula: TACTransFormula = this.transFormula,
        newTag: TACSummaryTag = this.tag
    ): TACSummaryWithTransFormula
}

interface TACSummary {
    val tag: TACSummaryTag
    val isNop: Boolean
    val isUnreachable: Boolean
}

sealed class TACSummaryTag {

    object Empty : TACSummaryTag()

    /** marks the initial summary that kicks of the project and prune summary generation*/
    object EmptyInitialProjectAndPrune : TACSummaryTag()

    data class TACCmdTag(val cmd: ComputeTACSummary.HasTACCommand) : TACSummaryTag() {
        override fun toString(): String = cmd.cmd.toString()
    }

    data class SequentialCompositionTag(val tag1: TACSummaryTag, val tag2: TACSummaryTag) : TACSummaryTag() {
        override fun toString(): String = "($tag1 . $tag2)"
    }

    data class ParallelCompositionTag(val tag1: TACSummaryTag, val tag2: TACSummaryTag) : TACSummaryTag() {
        override fun toString(): String = "($tag1 + $tag2)"
    }

    open fun sequentialComposition(other: TACSummaryTag): TACSummaryTag =
        SequentialCompositionTag(this, other)

    open fun parallelComposition(other: TACSummaryTag): TACSummaryTag =
        ParallelCompositionTag(this, other)

    companion object {
        fun sequentialComposition(tags: List<TACSummaryTag>): TACSummaryTag {
            return tags.reduceRight { l, r -> l.sequentialComposition(r) }
        }

        fun parallelComposition(tags: List<TACSummaryTag>): TACSummaryTag {
            return tags.reduceRight { l, r -> l.parallelComposition(r) }
        }
    }
}

/**
 * Represents something like "program variables", i.e., updatable variables, used to connect the variables in the proram
 * with the variables in the [TACTransFormula]s (which represent different values that the program variables assume over
 * time.
 */
data class TACSummaryVar(val sym: TACSymbol.Var) : Comparable<TACSummaryVar> {
    override fun toString(): String {
        return sym.toSMTRep()
    }

    override fun compareTo(other: TACSummaryVar): Int = this.toString().compareTo(other.toString())

    companion object {
        fun wrapVarSet(syms: Set<TACSymbol.Var>): Set<TACSummaryVar> {
            val res = mutableSetOf<TACSummaryVar>()
            syms.forEach { res.add(TACSummaryVar(it)) }
            return res
        }
    }
}
