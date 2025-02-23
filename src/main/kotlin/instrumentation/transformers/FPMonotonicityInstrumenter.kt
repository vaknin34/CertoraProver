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

package instrumentation.transformers

import analysis.maybeAnnotation
import analysis.maybeNarrow
import config.Config
import log.*
import optimizer.FREE_POINTER_SCALARIZED
import tac.Tag
import utils.mapNotNull
import vc.data.*
import datastructures.stdcollections.*
import optimizer.NO_MONOTONICITY_ASSUMPTIONS

private val logger = Logger(LoggerTypes.COMMON)

object FPMonotonicityInstrumenter {
    fun assumeStrictlyMonotonicFP(c: CoreTACProgram): CoreTACProgram {
        if (!Config.AssumeFPIsStrictlyMonotonic.get()) {
            return c
        }
        // make sure we find the free-pointer-is-scalarized annotation set to true everywhere
        // xxx consider running this pass last on scene-construction? will make much more sense
        val fpScalarizedEverywhere = c.parallelLtacStream().allMatch {
            // match on this boolean annotation, we want no instances that are false
            it.maybeAnnotation(FREE_POINTER_SCALARIZED) ?: true
        }
        if (!fpScalarizedEverywhere) {
            logger.info {"Program ${c.name} has calls where FP wasn't scalarized, skipping."}
            return c
        }

        val fpAssignments = c.parallelLtacStream().mapNotNull {
            it.maybeNarrow<TACCmd.Simple.AssigningCmd.AssignExpCmd>()?.takeIf {
                val lhsMeta = it.cmd.lhs.meta
                lhsMeta[TACSymbol.Var.KEYWORD_ENTRY]?.name == TACKeyword.MEM64.getName() &&
                    NO_MONOTONICITY_ASSUMPTIONS !in lhsMeta
            }
        }.sequential()
        return c.patching { patcher ->
            fpAssignments.forEach { fpAssignment ->
                val newFPValue = TACKeyword.TMP(Tag.Bit256, "!newFP").also{patcher.addVarDecl(it)}
                val monotonicityAssumeSym = TACKeyword.TMP(Tag.Bool, "!newFPMonotone").also{patcher.addVarDecl(it)}

                patcher.replaceCommand(
                    fpAssignment.ptr,
                    listOf(
                        TACCmd.Simple.LabelCmd("→ Assuming FP is strictly monotonic increasing"),
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(newFPValue, fpAssignment.cmd.rhs),
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(
                            monotonicityAssumeSym,
                            TACExpr.BinRel.Ge(newFPValue.asSym(), fpAssignment.cmd.lhs.asSym())
                        ),
                        TACCmd.Simple.AssumeCmd(monotonicityAssumeSym),
                        TACCmd.Simple.AssigningCmd.AssignExpCmd(fpAssignment.cmd.lhs, newFPValue),
                        TACCmd.Simple.LabelCmd("←")
                    )
                )
            }
        }
    }
}
