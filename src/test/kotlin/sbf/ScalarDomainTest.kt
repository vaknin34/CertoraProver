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
import sbf.analysis.ScalarAnalysis
import sbf.analysis.ScalarAnalysisRegisterTypes
import sbf.cfg.*
import sbf.disassembler.*
import sbf.domains.*
import sbf.testing.SbfTestDSL
import log.*
import org.junit.jupiter.api.*
import java.io.ByteArrayOutputStream
import java.io.PrintStream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class ScalarDomainTest {
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

    @Test
    fun test01() {
        sbfLogger.info { "====== TEST 1: StackEnvironment.overlap  =======" }
        val env = StackEnvironment<ScalarValue>()
        // check [20,28) is included [4,28)
        Assertions.assertEquals(true, env.overlap(ByteRange(20, 8), 4, 24, true))
        // check [24,32) is included in [4,28)
        Assertions.assertEquals(false, env.overlap(ByteRange(24, 8), 4, 24, true))
        // check [24,32) overlaps with [4,28)
        Assertions.assertEquals(true, env.overlap(ByteRange(24, 8), 4, 24, false))
        // check [28,36) overlaps with [4,28)
       Assertions.assertEquals(false, env.overlap(ByteRange(28, 8), 4, 24, false))
        // check [4,12) is included in [12,44]
        Assertions.assertEquals(false, env.overlap(ByteRange(4, 8), 12, 32, true))
        // check [8,16) overlaps with [12,44]
        Assertions.assertEquals(true, env.overlap(ByteRange(8, 8), 12, 32, false))
        // check [8,16) is included in [12,44]
        Assertions.assertEquals(false, env.overlap(ByteRange(8, 8), 12, 32, true))
    }

    @Test
    fun test02() {
        sbfLogger.info { "====== TEST 2: memcpy (last word)  =======" }
        /**
         *   r2 := r10 - 104
         *   *(r2 + 0):= 0
         *   *(r2 + 8):= 0
         *   *(r2 + 16):= 0
         *   *(r2 + 24):= 0
         *   r1 := r10 - 204
         *   r3 := 32
         *   memcpy(r1,r2,r3)
         *   assert(*(r1+24) == 0)
        **/

        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r2 = r10
                BinOp.SUB(r2, 104)
                r1 = r10
                BinOp.SUB(r1, 204)
                r2[0] = 0
                r2[8] = 0
                r2[16] = 0
                r2[24] = 0
                r3 = 32
                "sol_memcpy_"()
                r4 = r1[24]
                assert(CondOp.EQ(r4, 0))
            }
        }
        sbfLogger.warn {"$cfg"}
        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val b0 = cfg.getBlock(Label.Address(0))
        check (b0 != null)
        for (locInst in b0.getLocatedInstructions()) {
            val types = locInst.inst.readRegisters.map {
                Pair(it.r, regTypes.typeAtInstruction(locInst, it.r))
            }
            sbfLogger.warn {"Before ${locInst.inst} -> $types"}
            // We prove the assert by checking that the value of r4 is zero
            if (locInst.inst.isAssertOrSatisfy()) {
                val type = regTypes.typeAtInstruction(locInst, SbfRegister.R4_ARG)
                Assertions.assertEquals(type, SbfType.NumType(ConstantNum(0L)))
            }
        }
    }

    @Test
    fun test03() {
        sbfLogger.info { "====== TEST 3  =======" }
        /**
         *   r1 := 5
         *   r1 := r1 + 5
         **/

        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = 5
                BinOp.ADD(r1, 5)
            }
        }
        sbfLogger.warn {"$cfg"}
        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val b0 = cfg.getBlock(Label.Address(0))
        check (b0 != null)
        val addInst = b0.getLocatedInstructions().drop(1).first()
        val type = regTypes.typeAtInstruction(addInst, SbfRegister.R1_ARG)
        Assertions.assertEquals(true, type is SbfType.NumType && type.value.get() == 5L)
    }

    @Test
    fun test04() {
        sbfLogger.info { "====== TEST 4  =======" }
        /**
         *   assume(r1 == 5)
         *   assert(r1 == 5)
         **/

        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                assume(CondOp.EQ(r4, 5))
                assert(CondOp.EQ(r4, 5))
            }
        }
        sbfLogger.warn {"$cfg"}
        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val b0 = cfg.getBlock(Label.Address(0))
        check (b0 != null)
        val firstInst = b0.getLocatedInstructions().first()
        val firstType = regTypes.typeAtInstruction(firstInst, SbfRegister.R4_ARG)
        Assertions.assertEquals(true, firstType is SbfType.Top)
        val secondInst = b0.getLocatedInstructions().drop(1).first()
        val secondType = regTypes.typeAtInstruction(secondInst, SbfRegister.R4_ARG)
        Assertions.assertEquals(true, secondType is SbfType.NumType && secondType.value.get() == 5L)
    }

    @Test
    fun test05() {
        sbfLogger.info { "====== TEST 5: simple memory store and read =======" }
        /**
         *   r1 := r10 - 104
         *   *(r1+0) = 5
         *   assert( *(r1+0) == 5)
         **/

        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = r10
                BinOp.SUB(r1, 104)
                r1[0] = 5
                r1 = r1[0]
                assert(CondOp.EQ(r1, 5))
            }
        }
        sbfLogger.warn {"$cfg"}
        val globals:GlobalVariableMap = newGlobalVariableMap(56789L to SbfGlobalVariable("myglobal", 56789, 8))
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val b0 = cfg.getBlock(Label.Address(0))
        check (b0 != null)
        val loadInst = b0.getLocatedInstructions().drop(3).first()
        val loadBaseType = regTypes.typeAtInstruction(loadInst, SbfRegister.R1_ARG)
        sbfLogger.warn {"$loadInst -> $loadBaseType"}
        Assertions.assertEquals(true, loadBaseType is SbfType.PointerType.Stack && loadBaseType.offset.get()  == 3992L)

        val assertInst = b0.getLocatedInstructions().drop(4).first()
        val assertType = regTypes.typeAtInstruction(assertInst, SbfRegister.R1_ARG)
        sbfLogger.warn {"$assertInst -> $assertType"}
        Assertions.assertEquals(true, assertType is SbfType.NumType && assertType.value.get()  == 5L)

    }

    @Test
    fun test06() {
        sbfLogger.info { "====== TEST 6: implicit cast at memory store  =======" }
        /**
         *   r1 == 56789
         *   *(r1+0) = 0
         **/

        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = 56789
                r1[0] = 0
            }
        }
        sbfLogger.warn {"$cfg"}
        val globals: GlobalVariableMap = newGlobalVariableMap(56789L to SbfGlobalVariable("myglobal", 56789, 8))
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val b0 = cfg.getBlock(Label.Address(0))
        check (b0 != null)
        val secondInst = b0.getLocatedInstructions().drop(1).first()
        val secondType = regTypes.typeAtInstruction(secondInst, SbfRegister.R1_ARG)
        sbfLogger.warn {"$secondInst -> $secondType"}
       // Assertions.assertEquals(true, secondType is SbfType.NumType && secondType.value.get() == 5L)
    }

    @Test
    fun test07() {
        sbfLogger.info { "====== TEST 7: implicit cast at memory read  =======" }
        /**
         *   r1 == 56789
         *   r1 = *(r1+0)
         **/

        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = 56789
                r1[0] = 0
            }
        }
        sbfLogger.warn {"$cfg"}
        val globals: GlobalVariableMap = newGlobalVariableMap(56789L to SbfGlobalVariable("myglobal", 56789, 8))
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val b0 = cfg.getBlock(Label.Address(0))
        check (b0 != null)
        val secondInst = b0.getLocatedInstructions().drop(1).first()
        val secondType = regTypes.typeAtInstruction(secondInst, SbfRegister.R1_ARG)
        sbfLogger.warn {"$secondInst -> $secondType"}
        // Assertions.assertEquals(true, secondType is SbfType.NumType && secondType.value.get() == 5L)
    }

    @Test
    fun test08() {
        sbfLogger.info { "====== TEST 8 =======" }
        /**
         *  Example where the content of a stack offset is written and then copied (via memcpy) to another part of the stack.
         */
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r4 = r10
                BinOp.SUB(r4, 104)
                r4[0] = 5  // *sp(-104) := 5

                r2 = r10
                BinOp.SUB(r2, 504)
                r2[0] = r4

                r3 = 8
                r1 = r10
                BinOp.SUB(r1, 204)
                "sol_memcpy_"()
                r5 = r1[0]
                r5 = r5[0]
                assert(CondOp.EQ(r5, 5))
                exit()
            }
        }
        sbfLogger.warn {"$cfg"}
        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val b0 = cfg.getEntry()
        val sb = StringBuffer()
        for (locInst in b0.getLocatedInstructions()) {
            val inst = locInst.inst
            sb.append("$inst = {")
            for (reg in inst.readRegisters) {
                val type = regTypes.typeAtInstruction(locInst, reg.r)
                sb.append("$reg")
                sb.append(" -> ")
                sb.append("$type;")
            }
            sb.append("}\n")
            if (inst.isAssertOrSatisfy()) {
                val assertType = regTypes.typeAtInstruction(locInst, SbfRegister.R5_ARG)
                Assertions.assertEquals(true, assertType is SbfType.NumType && assertType.value.get()  == 5L)
            }
        }
        sbfLogger.warn {sb.toString()}
    }


    @Test
    fun test09() {
        sbfLogger.info { "====== TEST 9: two stores that overlap  =======" }
        /**
         *   r1 := r10 - 104
         *   *(r1+0) = 5
         *   *(r1+4) = 10
         *   assert( *(r1+0) == 5) // it shouldn't be probable
         **/

        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = r10
                BinOp.SUB(r1, 104)
                r1[0] = 5
                r1[4] = 10
                r1 = r1[0]
                assert(CondOp.EQ(r1, 5))
            }
        }
        sbfLogger.warn {"$cfg"}
        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val b0 = cfg.getBlock(Label.Address(0))
        check (b0 != null)

        val assertInst = b0.getLocatedInstructions().last()
        val assertType = regTypes.typeAtInstruction(assertInst, SbfRegister.R1_ARG)
        sbfLogger.warn {"$assertInst -> $assertType"}
        Assertions.assertEquals(false, assertType is SbfType.NumType && assertType.value.get()  == 5L)

    }

    @Test
    fun test10() {
        sbfLogger.info { "====== TEST 10: two contiguous stores with no overlaps  =======" }
        /**
         *   r1 := r10 - 104
         *   *(r1+0) = 5
         *   *(r1+8) = 10
         *   assert( *(r1+8) == 10) // it's true
         **/

        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = r10
                BinOp.SUB(r1, 104)
                r1[0] = 5
                r1[8] = 10
                r1 = r1[8]
                assert(CondOp.EQ(r1, 10))
            }
        }
        sbfLogger.warn {"$cfg"}
        val globals: GlobalVariableMap = newGlobalVariableMap(56789L to SbfGlobalVariable("myglobal", 56789, 8))
        val memSummaries = MemorySummaries()
        val scalarAnalysis = ScalarAnalysis(cfg, globals, memSummaries)
        val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)

        val b0 = cfg.getBlock(Label.Address(0))
        check (b0 != null)

        val assertInst = b0.getLocatedInstructions().last()
        val assertType = regTypes.typeAtInstruction(assertInst, SbfRegister.R1_ARG)
        sbfLogger.warn {"$assertInst -> $assertType"}
        Assertions.assertEquals(true, assertType is SbfType.NumType && assertType.value.get()  == 10L)

    }

}
