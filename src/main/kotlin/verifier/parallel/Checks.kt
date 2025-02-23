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

package verifier.parallel

import config.Config
import config.LocalSettings
import datastructures.stdcollections.*
import log.*
import smt.solverscript.LExpressionFactory
import smtlibutils.cmdprocessor.SmtFormulaCheckerResultWithChecker
import solver.SolverChoice
import statistics.data.TACProgramMetadata
import vc.data.CoreTACProgram
import vc.gen.LeinoWP
import verifier.ConstraintChooser
import verifier.LExpVcChecker
import verifier.LExpVcCheckerConfig
import verifier.TACVerifier.Companion.containsStorageComparisons
import verifier.UniqueSuccessorRemover
import verifier.splits.SplitTree
import kotlin.time.Duration
import kotlin.time.measureTimedValue

private suspend fun baseCheck(
    subProblem: SplitTree.Node,
    generatedTac: CoreTACProgram,
    timeout: Duration,
    tacProgramMetadata: TACProgramMetadata,
    check: suspend (LExpVcChecker) -> SmtFormulaCheckerResultWithChecker,
    localSettings: LocalSettings,
    configModifier: (LExpVcCheckerConfig) -> LExpVcCheckerConfig = { it },
): PartialResult {
    val lExpressionFactory = LExpressionFactory()

    val vcGenerationResult = measureTimedValue {
        val (collapsed, postprocessor) = UniqueSuccessorRemover.removeUniqueSuccessors(generatedTac)
        LeinoWP(collapsed, lExpressionFactory, tacProgramMetadata).generateVCs() to postprocessor
    }

    val (vc, postprocessor) = vcGenerationResult.value

    val config = configModifier(
        LExpVcCheckerConfig.fromLocalSettings(
            subProblem.name,
            lExpressionFactory.getUsedFeatures(),
            vc.tacProgram.containsStorageComparisons,
            timeout,
            localSettings
        )
    )

    val checkerResult = measureTimedValue {
        check(
            LExpVcChecker(
                timeout,
                vc,
                listOf(),
                lExpressionFactory,
                null,
                null,
                { prefix -> ArtifactManagerFactory().getFilePathForSmtQuery(prefix, null) },
                config,
            )
        )
    }

    return PartialResult(checkerResult.value, postprocessor, config, vc, checkerResult.duration)
}

suspend fun fullCheck(
    subProblem: SplitTree.Node,
    generatedTac: CoreTACProgram,
    timeout: Duration,
    tacProgramMetadata: TACProgramMetadata,
    localSettings: LocalSettings
    ): PartialResult = baseCheck(subProblem, generatedTac, timeout, tacProgramMetadata, {it.runCoreSolvers() }, localSettings) {
        it.copy(
            niaSolvers = SolverChoice(Config.ParallelSplitterNIASolvers.get().toList()),
            liaSolvers = SolverChoice(Config.ParallelSplitterLIASolvers.get().toList()),
            verifyWith = ConstraintChooser.entries,
        )
}

suspend fun quickCheck(
    subProblem: SplitTree.Node,
    generatedTac: CoreTACProgram,
    timeout: Duration,
    tacProgramMetadata: TACProgramMetadata,
    localSettings: LocalSettings
): PartialResult = baseCheck(subProblem, generatedTac, timeout, tacProgramMetadata, { it.quickSolve() }, localSettings)
