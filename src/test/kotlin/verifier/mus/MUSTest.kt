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

package verifier.mus

import config.Config
import config.ConfigScope
import kotlinx.coroutines.runBlocking
import loaders.WithTACSource
import log.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import smt.CoverageInfoEnum
import smt.solverscript.LExpressionFactory
import smtlibutils.cmdprocessor.SmtFormulaCheckerQuery
import smtlibutils.cmdprocessor.SmtFormulaCheckerResult
import smtlibutils.data.SatResult
import solver.Z3SolverInfo
import statistics.data.TACProgramMetadata
import vc.data.CoreTACProgram
import vc.gen.LExpVC
import vc.gen.LeinoWP
import verifier.LExpVcChecker
import verifier.LExpVcCheckerConfig
import verifier.RuleAndSplitIdentifier
import verifier.TACVerifier.Companion.containsStorageComparisons
import kotlin.time.Duration.Companion.seconds

/**
 * Test class for MUS enumeration feature implemented in the [MUSSubsetSolver] and [MUSMapSolver] classes.
 */
internal class MUSTest : WithTACSource {
    // Set a default config value - needed for the soft and hard constraint classification.
    private val baseScope = ConfigScope(Config.NumOfUnsatCores, 2)
        .extend(Config.CoverageInfoMode, CoverageInfoEnum.BASIC)

    // Set constants
    private val smallMUSPath = "verifier/mus/smallMUS.tac"
    private val sizeOfSmallMUS = 4
    private val simpleMUSPath = "verifier/mus/simpleMUS.tac"
    private val sizeOfSimpleMUS = 11
    private val experimentalMusPath = "verifier/mus/mus1.tac"
    private val sizeOfExperimentalMUS = 6
    private val intersectionSizeOfTwo = 5

    private val testName = RuleAndSplitIdentifier.dummyRoot("testProg")

    /**
     * input: [query] - query to be processed by the MUS solver
     *   [numOfMUSes] - maximal number of MUSes produced by the solver
     * output: MUSSubsetSolver on which the methods [MUSSubsetSolver.getMUSes] and
     *   [MUSSubsetSolver.getIntersection] can be called
     */
    private suspend fun getMUSSolver(query: SmtFormulaCheckerQuery, numOfMUSes: Int): MUSSubsetSolver {
        return ConfigScope(Config.NumOfUnsatCores, numOfMUSes).extend(Config.CoverageInfoMode, CoverageInfoEnum.BASIC).use {
            MUSSubsetSolver(
                query,
                Z3SolverInfo.plainConfig(5.seconds, incrementalMode = true)
            )
        }
    }

    /**
     * input: [tac] - CoreTACProgram to be verified
     *   [expectedSMTResult] - expected result of the SMT verification
     * output: query generated for the SMT verification
     */
    @OptIn(ArtifactManagerFactory.UsedOnlyInTests::class)
    private suspend fun getQuery(tac: CoreTACProgram, expectedSMTResult: SatResult? = null): SmtFormulaCheckerQuery {
        val lExpressionFactory = LExpressionFactory()

        val vc: LExpVC = LeinoWP(
            tac,
            lExpressionFactory,
            TACProgramMetadata(testName),
        ).generateVCs()
        val checker = LExpVcChecker(
            30.seconds,
            vc,
            datastructures.stdcollections.listOf(),
            //vc.tacProgram.name,
            lExpressionFactory,
            null,
            null,
            { prefix -> ArtifactManagerFactory(ArtifactManagerFactory.WithArtifactMode.WithoutArtifacts).getFilePathForSmtQuery(prefix, subdir = null) },
            LExpVcCheckerConfig.fromGlobalConfig(
                vc.tacProgram.name,
                lExpressionFactory.getUsedFeatures(),
                5.seconds,
                vc.tacProgram.containsStorageComparisons
            )
        )

        val checkerResult = checker.runSolvers().coreResult
        if (expectedSMTResult != null) {
            Assertions.assertEquals(expectedSMTResult, checkerResult.result.satResult)
        }
        val query = when (val res = checkerResult.result) {
            is SmtFormulaCheckerResult.Single -> res.query
            is SmtFormulaCheckerResult.Agg -> res.representativeResult.query
        }
        Assertions.assertNotEquals(null, query)

        return query!!
    }

    // All expressions in the TAC are part of the one MUS. All are returned.
    @Test
    fun checkTACWithLargerMUS() {
        runBlocking {
            baseScope.use {
                val tac = loadTACProgramResource(simpleMUSPath)
                val muses = getMUSSolver(getQuery(tac, SatResult.UNSAT), 1).getMUSes()

                Assertions.assertEquals(1, muses.size)
                Assertions.assertEquals(sizeOfSimpleMUS, muses.first().size)
            }
        }
    }

    // Most expressions in the TAC are not contained in the MUS. They are filtered away.
    @Test
    fun checkTACWithSmallMUS() {
        runBlocking {
            baseScope.use {
                val tac = loadTACProgramResource(smallMUSPath)
                val muses = getMUSSolver(getQuery(tac, SatResult.UNSAT), 1).getMUSes()

                Assertions.assertEquals(1, muses.size)
                Assertions.assertEquals(sizeOfSmallMUS, muses.first().size)
            }
        }
    }

    // TAC contains two MUSes. If only one is required, one is returned.
    @Test
    fun requireOneWhenMoreExist() {
        runBlocking {
            baseScope.use {
                val tac = loadTACProgramResource(experimentalMusPath)
                val muses = getMUSSolver(getQuery(tac, SatResult.UNSAT), 1).getMUSes()

                Assertions.assertEquals(1, muses.size)
                Assertions.assertEquals(sizeOfExperimentalMUS, muses.first().size)
            }
        }
    }

    // TAC contains two MUSes. If two are required, two are returned.
    @Test
    fun requireTwoWhenTwoExist() {
        runBlocking {
            baseScope.use {
                val tac = loadTACProgramResource(experimentalMusPath)
                val muses = getMUSSolver(getQuery(tac, SatResult.UNSAT), 2).getMUSes()

                Assertions.assertEquals(2, muses.size)
                Assertions.assertEquals(sizeOfExperimentalMUS, muses.first().size)
                Assertions.assertEquals(sizeOfExperimentalMUS, muses.last().size)
            }
        }
    }

    // TAC contains two MUSes. If ten are required, two are returned.
    @Test
    fun requireTenWhenTwoExist() {
        runBlocking {
            baseScope.use {
                val tac = loadTACProgramResource(experimentalMusPath)
                val muses = getMUSSolver(getQuery(tac, SatResult.UNSAT), 10).getMUSes()

                Assertions.assertEquals(2, muses.size)
                Assertions.assertEquals(sizeOfExperimentalMUS, muses.first().size)
                Assertions.assertEquals(sizeOfExperimentalMUS, muses.last().size)
            }
        }
    }

    // TAC contains two MUSes. If one is computed, the intersection is equal to the MUS.
    @Test
    fun testIntersectionOfOneMUS() {
        runBlocking {
            baseScope.use {
                val tac = loadTACProgramResource(experimentalMusPath)
                val musSolver = getMUSSolver(getQuery(tac, SatResult.UNSAT), 1)
                // First, the musSolver has to generate the MUSes before we can get the intersection.
                musSolver.getMUSes()
                val intersection = musSolver.getIntersection()

                Assertions.assertEquals(sizeOfExperimentalMUS, intersection.size)
            }
        }
    }

    // TAC contains two MUSes. If both are computed, the intersection is smaller than both of them.
    @Test
    fun testIntersectionOfTwoMUSes() {
        runBlocking {
            baseScope.use {
                val tac = loadTACProgramResource(experimentalMusPath)
                val musSolver = getMUSSolver(getQuery(tac, SatResult.UNSAT), 2)
                musSolver.getMUSes()
                val intersection = musSolver.getIntersection()

                Assertions.assertEquals(intersectionSizeOfTwo, intersection.size)
            }
        }
    }

    // Add test cases for timeouts when tac parsing is fixed.
}
