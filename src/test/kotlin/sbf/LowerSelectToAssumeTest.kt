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

package sbf

import com.certora.collect.*
import sbf.analysis.NPAnalysis
import sbf.cfg.*
import sbf.disassembler.*
import sbf.domains.*
import log.*
import org.junit.jupiter.api.*
import sbf.testing.SbfTestDSL
import java.io.ByteArrayOutputStream
import java.io.PrintStream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class LowerSelectToAssumeTest {
    private var outContent = ByteArrayOutputStream()
    private var errContent = ByteArrayOutputStream()

    private val originalOut = System.out
    private val originalErr = System.err

    // system properties have to be set before we load the logger
    @BeforeAll
    fun setupAll() {
        System.setProperty(LoggerTypes.SBF.toLevelProp(), "debug")
    }

    // we must reset our stream so that we could match on what we have in the current test
    @BeforeEach
    fun setup() {
        outContent = ByteArrayOutputStream()
        errContent = ByteArrayOutputStream()
        System.setOut(PrintStream(outContent, true)) // for 'always' logs
        System.setErr(PrintStream(errContent, true)) // loggers go to stderr
    }

    private fun debug() {
        originalOut.println(outContent.toString())
        originalErr.println(errContent.toString())
    }

    // close and reset
    @AfterEach
    fun teardown() {
        debug()
        System.setOut(originalOut)
        System.setErr(originalErr)
        outContent.close()
        errContent.close()
    }

    private fun getNumOfSelect(cfg: SbfCFG): UInt {
        var counter = 0U
        for (b in cfg.getBlocks().values) {
            counter += b.getInstructions().filterIsInstance<SbfInstruction.Select>().size.toUInt()
        }
        return counter
    }

    @Test
    fun test01() {
        val cfg = SbfTestDSL.makeCFG("test1", normalize = false) {
            bb(1) {
                r1 = 3
                select(r1, CondOp.EQ(r2, 1), 1, 0)
                assume(CondOp.EQ(r1, 1))
                assert(CondOp.EQ(r1, 1))
                exit()
            }
        }

        sbfLogger.warn { "Before $cfg" }
        cfg.verify(false)
        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val npAnalysis = NPAnalysis(cfg, globals, memSummaries)
        lowerSelectToAssume(cfg, npAnalysis)
        sbfLogger.warn { "After $cfg" }
        Assertions.assertEquals(true,  getNumOfSelect(cfg) == 0U)
    }

    @Test
    fun test02() {
        val cfg = SbfTestDSL.makeCFG("test2", normalize = false) {
            bb(1) {
                r1 = 3
                select(r1, CondOp.EQ(r2, 1), 1, 0)
                assert(CondOp.EQ(r1, 1))
                exit()
            }
        }

        sbfLogger.warn { "Before $cfg" }
        cfg.verify(false)
        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val npAnalysis = NPAnalysis(cfg, globals, memSummaries)
        lowerSelectToAssume(cfg, npAnalysis)
        sbfLogger.warn { "After $cfg" }
        Assertions.assertEquals(true,  getNumOfSelect(cfg) == 1U)
    }

    @Test
    fun test03() {
        val cfg = SbfTestDSL.makeCFG("test3", normalize = false) {
            bb(1) {
                r1 = 3
                select(r1, CondOp.EQ(r2, 1), 1, 0)
                assume(CondOp.EQ(r1, 1))
                r3 = 3
                select(r3, CondOp.EQ(r4, 1), 1, 0)
                assume(CondOp.EQ(r3, 1))
                assert(CondOp.EQ(r3, 1))
                exit()
            }
        }

        sbfLogger.warn { "Before $cfg" }
        cfg.verify(false)
        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val npAnalysis = NPAnalysis(cfg, globals, memSummaries)
        lowerSelectToAssume(cfg, npAnalysis)
        sbfLogger.warn { "After $cfg" }
        Assertions.assertEquals(true,  getNumOfSelect(cfg) == 0U)
    }

    @Test
    fun test04() {
        val cfg = SbfTestDSL.makeCFG("test4", normalize = false) {
            bb(1) {
                select(r1, CondOp.EQ(r2, 0), r3, 0)
                assume(CondOp.EQ(r1, 1))
                assert(CondOp.EQ(r1, 1))
                exit()
            }
        }

        sbfLogger.warn { "Before $cfg" }
        cfg.verify(false)
        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val npAnalysis = NPAnalysis(cfg, globals, memSummaries)
        lowerSelectToAssume(cfg, npAnalysis)
        sbfLogger.warn { "After $cfg" }
        Assertions.assertEquals(true,  getNumOfSelect(cfg) == 1U)
    }

}
