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

import analysis.TACCommandGraph
import datastructures.NonEmptyList
import datastructures.stdcollections.*
import log.*
import rules.FindReachabilityFailureSource
import scene.ISceneIdentifiers
import smtlibutils.cmdprocessor.SmtFormulaCheckerResult
import smtlibutils.data.ProcessDifficultiesResult
import smtlibutils.data.SatResult
import solver.SMTCounterexampleModel
import solver.toTacAssignment
import statistics.data.TACProgramMetadata
import vc.data.CoreTACProgram
import verifier.AbstractTACChecker
import verifier.splits.SplitAddress
import verifier.UniqueSuccessorRemover
import verifier.Verifier
import verifier.mus.UnsatCoreInputData
import kotlin.time.Duration

private val logger = Logger(LoggerTypes.COMMON)

/**
 * Note that [elapsedTime] includes axiom generation time and solver time (captures time for whole worklist
 * algo in [verifySingleSmtVc]).
 */
suspend fun verifierResultFromCheckerResult(
    scene: ISceneIdentifiers,
    tacProgramToVerify: CoreTACProgram,
    tacProgramMetadata: TACProgramMetadata,
    postprocessor: UniqueSuccessorRemover.ModelPostprocessor?,
    results: NonEmptyList<SmtFormulaCheckerResult>,
    elapsedTime: Duration,
    difficultyInfo: ProcessDifficultiesResult?,
    collapsedTacGraph: TACCommandGraph,
    unsatCoreSplitsData: Map<SplitAddress, UnsatCoreInputData>? = null
): Verifier.VerifierResult {

    /**
     * Generates an example-info given the result [result].
     */
    fun getExampleInfo(result: SmtFormulaCheckerResult): AbstractTACChecker.ExampleInfo {
        @Suppress("TooGenericExceptionCaught")
        val model = try {
            if (result.satResult is SatResult.SAT) {
                check(postprocessor != null) { "In case of SAT results, postprocessor has to be around." }
                SMTCounterexampleModel(
                    tacAssignments = postprocessor(result.toTacAssignment()),
                    havocedVariables = tacProgramToVerify.getHavocedSymbols()
                )
            } else {
                SMTCounterexampleModel.Empty
            }
        } catch (e: Exception) {
            logger.error(e) { "Error in parsing model ${result.getValuesResult}" }
            SMTCounterexampleModel.Empty
        }
        return AbstractTACChecker.ExampleInfo(model, result)
    }

    val examplesInfo = results
        .onEach { logger.debug { it } }
        .map(::getExampleInfo)
    val reachabilityIndicator =
        if (results.singleOrNull()?.satResult == SatResult.UNSAT) {
            FindReachabilityFailureSource.find(
                tacProgramMetadata.findReachabilityFailureSourceShouldCheckRule,
                tacProgramToVerify,
                scene
            )
        } else {
            null
        }

    return Verifier.VerifierResult(
        name = tacProgramToVerify.name,
        tac = tacProgramToVerify,
        elapsedTimeSeconds = elapsedTime.inWholeSeconds,
        reachabilityIndicator = reachabilityIndicator,
        difficultyInfo = difficultyInfo,
        examplesInfo = examplesInfo,
        unsatCoreSplitsData = unsatCoreSplitsData,
        unsolvedSplitsInfo = null,
        collapsedTACGraph = collapsedTacGraph,
        unsolvedSplitsPrograms = null
    ).also { verifierResult ->
        verifierResult.examplesInfo.onEach { exampleUniqueInfo ->
            exampleUniqueInfo.errorMessage?.let { logger.error { "Verification result contains error message: $it" } }
        }
    }
}
