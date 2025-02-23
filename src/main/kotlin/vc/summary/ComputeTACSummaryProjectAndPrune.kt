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
import datastructures.Bijection
import utils.containsAny
import vc.data.TACCmd
import vc.data.TACExpr
import vc.data.TACSymbol

/**
 * For now probably: ignore control flow blocks (assume statements)
 *
 * Prunes branches that revert (assumes they are unreachable).
 * Projects to values that are returned (effectively does cone-of-influence reduction wrt. them, albeit not a smart one,
 *  in that it does not know about arrays)
 *
 *   TODO: note that the control flow is not part of the "code" of the program (TACProgram.code) --> take that into account for summaries!
 *
 * @param projectedVars the variables whose values at the [sinks]
 */
class ComputeTACSummaryProjectAndPrune(
    private val projectedVars: Set<TACSymbol.Var>,
    val sinks: List<LTACCmd>,
    val settings: Settings
) : ComputeTACSummary<ComputeTACSummaryProjectAndPrune.ProjectAndPruneSummary> {
    private val projectedSumVars = projectedVars.map { TACSummaryVar(it) }.toSet()

    /**
     *
     * @param trackAssumes if this is set to 'true', assumes are added to the summary, their vars added to tracked vars for the
     *  cone-of-influence
     *
     * @param markReturnedVarForTracking if this is set to 'true', then variables occurring in a `ReturnCmd` are added to tracked vars for the
     *  cone-of-influence
     */
    data class Settings(val trackAssumes: Boolean, val markReturnedVarForTracking: Boolean) {
        companion object {
            val Default = Settings(trackAssumes = false, markReturnedVarForTracking = false)
        }
    }

    val projectorDummy = ProjectAndPruneSummary(
        ComputeTACSummaryTransFormula.TACSummaryTransFormula.SimpleTACSummaryTransFormula(
            TACTransFormula.True,
            TACSummaryTag.EmptyInitialProjectAndPrune,
            false,
            false
        ),
        projectedSumVars,
        setOf(),
        projectedSumVars
    )

    val computeTACSummaryTransFormula = ComputeTACSummaryTransFormula()

    override fun parallelComposition(rs: List<ProjectAndPruneSummary>): ProjectAndPruneSummary {
        if (rs.any { it is AbsorberUnreachSummary }) {
            error { "should not happen (regex/tarjan approach should have dealt with this)" }
        }

        val useSet = mutableSetOf<TACSummaryVar>() // first.useSet + second.useSet
        val defSet = mutableSetOf<TACSummaryVar>() // first.defSet + second.defSet
        val varsToProjectTo = mutableSetOf<TACSummaryVar>()// first.varsToProjectTo + second.varsToProjectTo
        rs.forEach {
            useSet.addAll(it.useSet)
            defSet.addAll(it.defSet)
            varsToProjectTo.addAll(it.varsToProjectTo)
        }

        return ProjectAndPruneSummary(
            computeTACSummaryTransFormula.parallelComposition(rs.map { it.tfSum }),
            useSet,
            defSet,
            varsToProjectTo
        )
    }

    override fun sequentialComposition(rs: List<ProjectAndPruneSummary>): ProjectAndPruneSummary {
        check(!rs.any { it is AbsorberUnreachSummary }) { "should not happen if we're using Tarjan/Regex approach" }
        check(associativityRequirement == AssociativityRequirement.FORCE_TIMES_RIGHTASSOCIATIVE)

        var currDefSet = setOf<TACSummaryVar>()
        var currUseSet = setOf<TACSummaryVar>()
        var currMarkedVars = setOf<TACSummaryVar>()

        val projectedSumsBw = mutableListOf<ComputeTACSummaryTransFormula.TACSummaryTransFormula>()

        val projectedVarDefinersRev = mutableSetOf<Int>()

        rs.asReversed().forEachIndexed { index, currPpSum ->

            if (!currPpSum.defSet.containsAny(currMarkedVars) && currPpSum.varsToProjectTo.isEmpty()) {
                // replace the statement with a nop (as placeholder, for transparency)
                projectedSumsBw.add(ComputeTACSummaryTransFormula.TACSummaryTransFormula.buildNop(currPpSum.tfSum.tag))
            } else {
                val newUseSet = (currUseSet - currPpSum.defSet) + currPpSum.useSet
                val newDefSet = currDefSet + currPpSum.defSet
                val newMarkedVars = (currMarkedVars - currPpSum.defSet) + currPpSum.useSet + currPpSum.varsToProjectTo

                val markedAndProjectedOld = currMarkedVars.filter { it in projectedSumVars }
                val projectedVarsThatAreNoLongerMarked =
                    projectedSumVars.filter { it in markedAndProjectedOld && it !in newMarkedVars }
                if (projectedVarsThatAreNoLongerMarked.isNotEmpty())
                    projectedVarDefinersRev.add(index)

                currUseSet = newUseSet
                currDefSet = newDefSet
                currMarkedVars = newMarkedVars


                projectedSumsBw.add(currPpSum.tfSum)
            }
        }

        val projectedVarDefiners = projectedVarDefinersRev.map { rs.size - 1 - it }

        val res = computeTACSummaryTransFormula.sequentialComposition(projectedSumsBw.asReversed())
        val (tfSum, ssaConjuncts, _, ssaDefs) = res.seqCompResult

        val projectedVarDefinersFullyInlined = projectedVarDefiners.map { definerIndex ->
            val ssaConjunct = ssaConjuncts[definerIndex] as TACExpr.BinRel.Eq
            val substituted =
                SaturateSubstitutionTACExpr(ssaDefs.mapValues { it.value.exp }).submit(listOf(ssaConjunct.o2))
            val assignedVars = rs[definerIndex].tfSum.transFormula.assignedVars
            val outVars = assignedVars.map { it to (tfSum.outVars[it] ?: error("outvar not found?")) }
            TACTransFormula(
                ssaConjunct.copy(o2 = substituted),
                tfSum.inVars,
                Bijection.fromPairs(outVars),
                assignedVars,
                tfSum.auxVars
            )
        }
        val sum =  when (projectedVarDefinersFullyInlined.size) {
            0 -> res
            1 -> ComputeTACSummaryTransFormula.TACSummaryTransFormula.SimpleTACSummaryTransFormula(
                projectedVarDefinersFullyInlined.first(), res.tag, isNop = false, isUnreachable = false
            )
            else -> throw UnsupportedOperationException("TODO: generalize -- " +
                    "(cases that I don't expect to be covered, yet: tuples, assumes, multiple return locations, " +
                    "side effects ")
        }

        return ProjectAndPruneSummary(
            sum,
            currUseSet,
            currDefSet,
            currMarkedVars
        )
    }

    override fun summarizeCmd(cmd: ComputeTACSummary.HasTACCommand): ProjectAndPruneSummary {

        val sum = when (val c = cmd.cmd) {
            is TACCmd.Simple.AssigningCmd -> {
                val tfSum = computeTACSummaryTransFormula.summarizeCmd(cmd)
                val useSet = TACSummaryVar.wrapVarSet(c.getFreeVarsOfRhs())
                val defSet = TACSummaryVar.wrapVarSet(setOf(c.lhs))
                ProjectAndPruneSummary(
                    tfSum,
                    useSet,
                    defSet,
                    setOf()
                )
            }
            is TACCmd.Simple.WordStore -> {
                val tfSum = computeTACSummaryTransFormula.summarizeCmd(cmd)
                val useSet = TACSummaryVar.wrapVarSet(c.getFreeVarsOfRhs())
                val defSet = TACSummaryVar.wrapVarSet(setOf(c.base))
                ProjectAndPruneSummary(tfSum, useSet, defSet, setOf())
            }
            is TACCmd.Simple.RevertCmd -> AbsorberUnreachSummary
            is TACCmd.Simple.ReturnCmd -> {
                if (settings.markReturnedVarForTracking) {
                    val tfSum = computeTACSummaryTransFormula.summarizeCmd(cmd)
                    val useSet = listOf(c.memBaseMap, c.o1, c.o2).filterIsInstance<TACSymbol.Var>()
                        .map { TACSummaryVar(it) }.toSet()
                    val defSet: Set<TACSummaryVar> = setOf()
                    // use [useSet] also for [varsToProjectTo] parameter
                    ProjectAndPruneSummary(
                        tfSum,
                        useSet,
                        defSet,
                        varsToProjectTo = useSet
                    )
                } else {
                    val nop = ComputeTACSummaryTransFormula.TACSummaryTransFormula.buildNop(cmd)
                    ProjectAndPruneSummary(nop, setOf(), setOf(), setOf())
                }
            }
            is TACCmd.Simple.ReturnSymCmd -> {
                if (settings.markReturnedVarForTracking) {
                    val tfSum = computeTACSummaryTransFormula.summarizeCmd(cmd)
                    val useSet = listOf(c.o).filterIsInstance<TACSymbol.Var>().map { TACSummaryVar(it) }.toSet()
                    val defSet: Set<TACSummaryVar> = setOf()
                    // use [useSet] also for [varsToProjectTo] parameter
                    ProjectAndPruneSummary(
                        tfSum,
                        useSet,
                        defSet,
                        varsToProjectTo = useSet
                    )
                } else {
                    val nop = ComputeTACSummaryTransFormula.TACSummaryTransFormula.buildNop(cmd)
                    ProjectAndPruneSummary(nop, setOf(), setOf(), setOf())
                }
            }
            is TACCmd.Simple.AssumeCmd -> {
                summarizeAssume(cmd, c.cond)
            }
            is TACCmd.Simple.AssumeNotCmd -> {
                summarizeAssume(cmd, c.cond)
            }
            else -> {
                // TODO: ultimately eliminate this, perhaps? -- we just ignore those commands..
                val nop = ComputeTACSummaryTransFormula.TACSummaryTransFormula.buildNop(cmd)
                ProjectAndPruneSummary(nop, setOf(), setOf(), setOf())
            }
        }

        return if ((cmd as? ComputeTACSummary.HasTACCommand.LTACCmd)?.ltacCmd in sinks) {
            sequentialComposition(listOf(sum, projectorDummy))
        } else {
            sum
        }
    }

    override fun summarizeLoop(loopBody: ProjectAndPruneSummary): ProjectAndPruneSummary {
        throw UnsupportedOperationException("not implemented summarizeLoop for $loopBody") //To change body of created functions use File | Settings | File Templates.
    }


    private fun summarizeAssume(hasTacCmd: ComputeTACSummary.HasTACCommand, cond: TACSymbol): ProjectAndPruneSummary {
        val cmd = hasTacCmd.cmd
        if (cmd !is TACCmd.Simple.AssumeCmd && cmd !is TACCmd.Simple.AssumeNotCmd) {
            error("only accepts assumes")
        }
        return if (settings.trackAssumes) {
            val defaultSummary = computeTACSummaryTransFormula.summarizeCmd(hasTacCmd)
            val useSet = TACSummaryVar.wrapVarSet(
                when (cmd) {
                    is TACCmd.Simple.AssumeCmd -> if (cmd.cond is TACSymbol.Var) setOf(cond as TACSymbol.Var) else setOf()
                    is TACCmd.Simple.AssumeNotCmd -> if (cmd.cond is TACSymbol.Var) setOf(cond as TACSymbol.Var) else setOf()
                    else -> error("only accepts assumes")
                }
            )
            AssumeProjectAndPruneSummary(
                defaultSummary,
                useSet,
                setOf(),
                useSet
            )
        } else {
            val nop = ComputeTACSummaryTransFormula.TACSummaryTransFormula.buildNop(hasTacCmd)
            ProjectAndPruneSummary(
                nop,
                setOf(),
                setOf(),
                setOf()
            )
        }
    }


    /**
     *
     * @param varsToProjectTo the variables we care about
     */
    open class ProjectAndPruneSummary(
        open val tfSum: ComputeTACSummaryTransFormula.TACSummaryTransFormula,
        open val useSet: Set<TACSummaryVar>,
        open val defSet: Set<TACSummaryVar>,
        open val varsToProjectTo: Set<TACSummaryVar>
    ) : ToLExpTransformula {

        override fun getTACSummaryTransformula(): ComputeTACSummaryTransFormula.TACSummaryTransFormula = tfSum

        fun copy(
            newTransFormula: TACTransFormula = this.tfSum.transFormula,
            newTag: TACSummaryTag = this.tfSum.tag
        ): ProjectAndPruneSummary {
            return ProjectAndPruneSummary(
                tfSum.copy(newTransFormula, newTag),
                this.useSet,
                this.defSet,
                this.varsToProjectTo
            )
        }

        override fun toString(): String {
            return tfSum.toString()
        }
    }

    object AbsorberUnreachSummary : ProjectAndPruneSummary(
        ComputeTACSummaryTransFormula.TACSummaryTransFormula.SimpleTACSummaryTransFormula(
            TACTransFormula.False,
            TACSummaryTag.Empty,
            isUnreachable = true
        ), setOf(), setOf(), setOf()
    )

    data class AssumeProjectAndPruneSummary(
        override val tfSum: ComputeTACSummaryTransFormula.TACSummaryTransFormula,
        override val useSet: Set<TACSummaryVar>,
        override val defSet: Set<TACSummaryVar>,
        override val varsToProjectTo: Set<TACSummaryVar>
    ) : ProjectAndPruneSummary(tfSum, useSet, defSet, varsToProjectTo)

    override val associativityRequirement = AssociativityRequirement.FORCE_TIMES_RIGHTASSOCIATIVE


}
