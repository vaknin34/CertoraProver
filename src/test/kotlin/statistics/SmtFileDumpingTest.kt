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

package statistics

import config.ConfigScope
import config.ConfigType
import io.mockk.every
import io.mockk.mockkObject
import io.mockk.slot
import io.mockk.unmockkAll
import kotlinx.coroutines.runBlocking
import log.*
import org.junit.jupiter.api.AfterEach
import org.junit.jupiter.api.Assertions.assertTrue
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import smtlibutils.cmdprocessor.*
import smtlibutils.data.FactorySmtScript
import smtlibutils.parser.SMTParser
import utils.mapSecond
import vc.data.TACBuilderAuxiliaries
import verifier.Executable
import kotlin.time.Duration

internal class SmtFileDumpingTest : TACBuilderAuxiliaries() {

    private var usedArtifacts = mutableListOf<String>()
    private val configScope = ConfigScope(ConfigType.WithArtifacts, ArtifactManagerFactory.WithArtifactMode.WithoutArtifacts)

    @BeforeEach
    fun beforeTest() {
        configScope.use {

        mockkObject(ArtifactManagerFactory())

        usedArtifacts = mutableListOf<String>()

        val name = slot<String>()

        every {
            ArtifactManagerFactory().registerArtifact(capture(name), any())
        } answers {
            usedArtifacts.add(name.captured)
            name.captured
        }

        }

    }

    @AfterEach
    fun afterTest() {
        unmockkAll()
    }

    /** Call dumping with an [SmtFormulaCheckerResult] that results from the solver crashing because we gave it a
     * negative timeout. */
    @Test
    fun negativeTimeout() {
        configScope.use {
            val negTimeout = Duration.parse("-PT5.0S")
            val z3 = SimpleFormulaChecker.plainZ3Spawner(
                timeout = negTimeout,
                script = FactorySmtScript,
                dumpFile = null
            )
            check(z3 != null) { "failed to create the z3Spawner that we need for this test" }
            lateinit var checkerInstance: SmtFormulaChecker
            val emptyFormula = SMTParser.parseText(
                """
                    (set-logic ALL)
                    (check-sat)
                """.trimIndent()
            ).toSmtFormula()
            val query = SmtFormulaCheckerQuery(
                SmtFormulaCheckerQueryInfo(name = "test"),
                smtFormula = emptyFormula,
            )


            val artifactName = "fromEmptyQueryWithNegativeTimeout"
            runBlocking {
                val (_, res) = try {
                    checkerInstance = z3() // z3 will crash on startup due to negative timeout
                    "success" to checkerInstance.check(query)
                } catch (e: Exception) {
                    Executable.handleNonConcurrencyRelatedExceptions(e, checkerInstance, query).mapSecond { r -> r.result }
                }
                SmtFileDumping.dumpFormulaAndOrProgram(artifactName, res, null)
            }

            /* check that the artifact name is contained in the name of the artifact that would have been dumped */
            assertTrue(artifactName in usedArtifacts.single())
        }
    }
    /*
    @Test
    fun testReportMisc01() {
        val p = TACProgramBuilder {
            x assign bool(true)
        }.code

        SmtFileDumping.reportMiscProblem(null, "testSFDT", p)
    }
     */

}
