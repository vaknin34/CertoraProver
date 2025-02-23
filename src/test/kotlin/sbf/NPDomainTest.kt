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
import config.ConfigScope
import sbf.analysis.ScalarAnalysis
import sbf.analysis.ScalarAnalysisRegisterTypes
import sbf.analysis.NPAnalysis
import sbf.cfg.*
import sbf.disassembler.Label
import sbf.disassembler.newGlobalVariableMap
import sbf.domains.MemorySummaries
import sbf.domains.VariableFactory
import sbf.domains.NPDomain
import sbf.testing.SbfTestDSL
import log.*
import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.Test
import java.io.ByteArrayOutputStream
import java.io.PrintStream
import org.junit.jupiter.api.*

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class NPDomainTest {
    private var outContent = ByteArrayOutputStream()
    private var errContent = ByteArrayOutputStream()

    private val originalOut = System.out
    private val originalErr = System.err

    // system properties have to be set before we load the logger
    @BeforeAll
    fun setupAll() {
        System.setProperty(LoggerTypes.SBF.toLevelProp(), "info")
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


    @Test
    fun test01() {
        /*
             *(r10 - 104) := 0
             r3:= *(r10 - 104)
             r2 := r3
             r1 := r2
             assume(r1 == 5)
         */
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r10[-104] = 0
                r3 = r10[-104]
                r2 = r3
                r1 = r2
                assume(CondOp.EQ(r1, 5))
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val vFac = VariableFactory()
        val absVal = NPDomain.mkTrue()
        val b = cfg.getBlock(Label.Address(0))
        check(b!=null)
        val newAbsVal = absVal.analyze(b, vFac, regTypes, false)
        sbfLogger.info{"absVal=$absVal\n$b\n newAbsVal=$newAbsVal"}
        Assertions.assertEquals(true, newAbsVal.isBottom())
    }

    @Test
    fun test02() {
        /*
             r4 : = 1
             *(r10 - 104) := 1
             r3:= *(r10 - 104)
             r2 := r3
             r2 -= r4
             r1 := r2
             r1 += 1
             assume(r1 == 0)
         */

        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r4 = 1
                r10[-104] = 1
                r3 = r10[-104]
                r2 = r3
                BinOp.SUB(r2, 1)
                r1 = r2
                BinOp.ADD(r1, 1)
                assume(CondOp.EQ(r1, 0))
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)

        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val vFac = VariableFactory()
        val absVal = NPDomain.mkTrue()
        val b = cfg.getBlock(Label.Address(0))
        check(b!=null)
        val newAbsVal = absVal.analyze(b, vFac, regTypes, false)
        sbfLogger.info{"absVal=$absVal\n$b\n newAbsVal=$newAbsVal"}
        Assertions.assertEquals(true, newAbsVal.isBottom())
    }

    @Test
    fun test03() {
        /*
             r3  := r10 - 96
             *(r10 - 104) := r3
             r2  := *(r10 - 104)
             *r2 := 0
             r1  := *(r10 - 96)
             assume(r1 > 5)
         */
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r3 = r10
                BinOp.SUB(r3, 96)
                r10[-104] = r3
                r2 = r10[-104]
                r2[0] = 0
                r1 = r10[-96]
                assume(CondOp.GT(r1, 5))
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val vFac = VariableFactory()
        val absVal = NPDomain.mkTrue()
        val b = cfg.getBlock(Label.Address(0))
        check(b!=null)
        val newAbsVal = absVal.analyze(b, vFac, regTypes, false)
        sbfLogger.info{"absVal=$absVal\n$b\nnewAbsVal=$newAbsVal"}
        Assertions.assertEquals(true, newAbsVal.isBottom())
    }

    @Test
    fun test04() {
        /*
             assume(r4 != 0)
             assume(r4 == 0)
         */
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                assume(CondOp.NE(r4, 0))
                assume(CondOp.EQ(r4, 0))
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val vFac = VariableFactory()
        val absVal = NPDomain.mkTrue()
        val b = cfg.getBlock(Label.Address(0))
        check(b!=null)
        val newAbsVal = absVal.analyze(b, vFac, regTypes, false)
        sbfLogger.info{"absVal=$absVal\n$b\nnewAbsVal=$newAbsVal"}
        Assertions.assertEquals(true, newAbsVal.isBottom())
    }

    @Test
    fun test05() {
        /*
             assume(r4 == 0)
             assume(r4 != 0)
         */
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                assume(CondOp.EQ(r4, 0))
                assume(CondOp.NE(r4, 0))
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val vFac = VariableFactory()
        val absVal = NPDomain.mkTrue()
        val b = cfg.getBlock(Label.Address(0))
        check(b!=null)
        val newAbsVal = absVal.analyze(b, vFac, regTypes, false)
        sbfLogger.info{"absVal=$absVal\n$b\nnewAbsVal=$newAbsVal"}
        Assertions.assertEquals(true, newAbsVal.isBottom())
    }

    @Test
    fun test06() {
        /*
             assume(r4 == 0)
             assume(r4 > 5)
         */
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                assume(CondOp.EQ(r4, 0))
                assume(CondOp.GT(r4, 5))
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val vFac = VariableFactory()
        val absVal = NPDomain.mkTrue()
        val b = cfg.getBlock(Label.Address(0))
        check(b!=null)
        val newAbsVal = absVal.analyze(b, vFac, regTypes, false)
        sbfLogger.info{"absVal=$absVal\n$b\nnewAbsVal=$newAbsVal"}
        Assertions.assertEquals(true, newAbsVal.isBottom())
    }

    @Test
    fun test07() {
        /*   // Example where propagation is too weak
             assume(r4 < 3)
             assume(r4 > 5)
         */
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                assume(CondOp.LT(r4, 3))
                assume(CondOp.GT(r4, 5))
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val vFac = VariableFactory()
        val absVal = NPDomain.mkTrue()
        val b = cfg.getBlock(Label.Address(0))
        check(b!=null)
        val newAbsVal = absVal.analyze(b, vFac, regTypes, false)
        sbfLogger.info{"absVal=$absVal\n$b\nnewAbsVal=$newAbsVal"}
        Assertions.assertEquals(false, newAbsVal.isBottom())
    }

    @Test
    fun test8() {
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = r10
                BinOp.SUB(r1, 96)
                r2 = r10
                BinOp.SUB(r2, 296)
                br(CondOp.EQ(r3, 0x1), 1, 2)
            }
            bb(1) {
                r4 = r2[16]
                assume(CondOp.EQ(r4, 11))
                goto(3)
            }
            bb(2) {
                r4 = r2[16]
                assume(CondOp.EQ(r4, 7))
                goto(3)
            }
            bb(3) {
                r2[0] = 5
                r3 = 24
                "sol_memcpy_"()
                r4 = r1[16]
                assume(CondOp.EQ(r4, 7))
                r4 = r2[8]
                assume(CondOp.EQ(r4, 10))
                assert(CondOp.EQ(r4, 10)) // added assert so that NPAnalysis runs
                exit()
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val np = NPAnalysis(cfg, globals, memSummaries)
        val absValAt1 = np.getPreconditionsAtEntry(Label.Address(1))
        check(absValAt1 != null){"No preconditions for label 1"}
        val absValAt2 = np.getPreconditionsAtEntry(Label.Address(2))
        check(absValAt2 != null){"No preconditions for label 2"}


        sbfLogger.warn{"absVal at 1=$absValAt1\nAbsVal at 2=$absValAt2"}
        Assertions.assertEquals(true, absValAt1.isBottom())
        Assertions.assertEquals(false, absValAt2.isBottom())
    }

    @Test
    fun test9() {
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r2 = r10[-96]
                br(CondOp.NE(r2, 0x1), 1, 2)
            }
            bb(1) {
                assume(CondOp.NE(r2, 0x1))
                r3 = r10[-96]
                assume(CondOp.EQ(r3, 0x1))
                goto(3)
            }
            bb(2) {
                assume(CondOp.EQ(r2, 0x1))
                goto(3)
            }
            bb(3) {
                assert(CondOp.EQ(r4, 0)) // added assert so that NPAnalysis runs
                exit()
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val np = NPAnalysis(cfg, globals, memSummaries)
        val absValAt1 = np.getPreconditionsAtEntry(Label.Address(1))
        check(absValAt1 != null){"No preconditions for label 1"}
        sbfLogger.warn {"$cfg"}
        sbfLogger.warn {"Preconditions at entry of 1=$absValAt1\n"}

        Assertions.assertEquals(true, absValAt1.isBottom())
    }

    @Test
    fun test10() {
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = 1
                br(CondOp.NE(r9, 0x0), 1, 2)
            }
            bb(1) {
                assume(CondOp.NE(r9, 0x0))
                goto(3)
            }
            bb(2) {
                assume(CondOp.EQ(r9, 0x0))
                r1 = 0
                goto(3)
            }
            bb(3) {
                // If we propagate backwards r9 != 0 then this assertion will be always true, which is unsound
                assert(CondOp.NE(r1, 0))
                assume(CondOp.NE(r9, 0))
                BinOp.MUL(r8, r7)
                BinOp.DIV(r8, r9)
                assert(CondOp.NE(r2, 0))  // added unrelated assert so that NPAnalysis starts from here
                exit()
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        sbfLogger.warn { "$cfg" }

        ConfigScope(SolanaConfig.SlicerBackPropagateThroughAsserts, true).use {
            val np = NPAnalysis(cfg, globals, memSummaries)
            val absValAt1 = np.getPreconditionsAtEntry(Label.Address(1))
            check(absValAt1 != null) { "No preconditions for label 1" }
            sbfLogger.warn { "Preconditions at entry of 1=$absValAt1\n" }
            val absValAt2 = np.getPreconditionsAtEntry(Label.Address(2))
            check(absValAt2 != null) { "No preconditions for label 2" }
            sbfLogger.warn { "Preconditions at entry of 2=$absValAt2\n" }
            val absValAt3 = np.getPreconditionsAtEntry(Label.Address(3))
            check(absValAt3 != null) { "No preconditions for label 3" }
            sbfLogger.warn { "Preconditions at entry of 3=$absValAt3\n" }
            Assertions.assertEquals(true, absValAt2.isBottom())
        }
    }

    @Test
    // Same as test10 but disabling SlicerBackPropagateThroughAsserts
    fun test11() {
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = 1
                br(CondOp.NE(r9, 0x0), 1, 2)
            }
            bb(1) {
                assume(CondOp.NE(r9, 0x0))
                goto(3)
            }
            bb(2) {
                assume(CondOp.EQ(r9, 0x0))
                r1 = 0
                goto(3)
            }
            bb(3) {
                assert(CondOp.NE(r1, 0))
                assume(CondOp.NE(r9, 0))
                BinOp.MUL(r8, r7)
                BinOp.DIV(r8, r9)
                assert(CondOp.NE(r2, 0))  // added assert so that NPAnalysis starts from here
                exit()
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        sbfLogger.warn { "$cfg" }

        ConfigScope(SolanaConfig.SlicerBackPropagateThroughAsserts, false).use {
            val np = NPAnalysis(cfg, globals, memSummaries)
            val absValAt1 = np.getPreconditionsAtEntry(Label.Address(1))
            check(absValAt1 != null) { "No preconditions for label 1" }
            sbfLogger.warn { "Preconditions at entry of 1=$absValAt1\n" }
            val absValAt2 = np.getPreconditionsAtEntry(Label.Address(2))
            check(absValAt2 != null) { "No preconditions for label 2" }
            sbfLogger.warn { "Preconditions at entry of 2=$absValAt2\n" }
            val absValAt3 = np.getPreconditionsAtEntry(Label.Address(3))
            check(absValAt3 != null) { "No preconditions for label 3" }
            sbfLogger.warn { "Preconditions at entry of 3=$absValAt3\n" }
            Assertions.assertEquals(false, absValAt2.isBottom())
        }
    }
}


