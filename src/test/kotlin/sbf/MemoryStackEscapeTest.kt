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
import datastructures.stdcollections.*
import sbf.analysis.ScalarAnalysis
import sbf.analysis.ScalarAnalysisRegisterTypes
import sbf.analysis.WholeProgramMemoryAnalysis
import sbf.callgraph.MutableSbfCallGraph
import sbf.cfg.*
import sbf.disassembler.newGlobalVariableMap
import sbf.domains.*
import sbf.support.PointerStackEscapingError
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
class MemoryStackEscapeTest {
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
        sbfLogger.info { "====== TEST 1 =======" }
        /**
         *  The scalar domain is sound assuming that no stack address escapes.
         *  The pointer domain is sound without that assumption.
         *
         *  This is an example where a stack address (offset 3992) is stored in the heap and then modified.
         */
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r2 = r10
                BinOp.SUB(r2, 104)
                r2[0] = 5  // *sp(-104) := 5
                r1 = r10
                BinOp.SUB(r1, 96)
                r3 = 16
                "__rust_alloc"()
                r0[0] = r2 // sp(-104) escapes
                r1[0] = r0
                r4 = r0[0]
                r4[0] = 2 // *sp(-104) := 2
                r5 = r2[0]
                assert(CondOp.EQ(r5, 2)) // The scalar domain infers incorrectly that r5 == 5
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

            sb.append("${locInst.inst} = {")
            for (reg in locInst.inst.readRegisters) {
                val type = regTypes.typeAtInstruction(locInst, reg.r)
                sb.append("$reg")
                sb.append(" -> ")
                sb.append("$type;")
            }
            sb.append("}\n")
        }
        sbfLogger.warn {sb.toString()}

        val prog = MutableSbfCallGraph(mutableListOf(cfg), setOf("entrypoint"), globals)
        val memAnalysis = WholeProgramMemoryAnalysis(prog, memSummaries)
        var exception = false
        try {
            memAnalysis.inferAll()
        } catch (e: PointerStackEscapingError) {
            // The pointer analysis should throw an exception because stack is escaping
            exception = true
        }
        Assertions.assertEquals(true, exception)
    }

    @Test
    fun test02() {
        sbfLogger.info { "====== TEST 2 =======" }
        /**
         *  The scalar domain is sound assuming that no stack address escapes.
         *  The pointer domain is sound without that assumption.
         *
         *  Similar to test02 but the stack offset 3992 escapes via a memcpy instruction
         */
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r4 = r10
                BinOp.SUB(r4, 104)
                r4[0] = 5  // *sp(3992) := 5

                r1 = 8
                "__rust_alloc"()
                r1 = r10
                BinOp.SUB(r1, 504)
                r1[0] = r0 // *sp(3592) -> heap

                r2 = r10
                BinOp.SUB(r2, 204) //*sp(3892) := sp(3992)
                r2[0] = r4

                r3 = 8
                r1 = r1[0]
                "sol_memcpy_"() // sp(3992) escapes here, and it is stored in the heap
                r5 = r1[0]
                r5 = r5[0]
                r5[0] = 10  // because sp(3992) here we are actually doing sp(3992) := 10

                r5 = r4[0]
                assert(CondOp.EQ(r5, 10))  // The scalar domain infers incorrectly that r5 == 5
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

            sb.append("${locInst.inst} = {")
            for (reg in locInst.inst.readRegisters) {
                val type = regTypes.typeAtInstruction(locInst, reg.r)
                sb.append("$reg")
                sb.append(" -> ")
                sb.append("$type;")
            }
            sb.append("}\n")
        }
        sbfLogger.warn {sb.toString()}

        val prog = MutableSbfCallGraph(mutableListOf(cfg), setOf("entrypoint"), globals)
        val memAnalysis = WholeProgramMemoryAnalysis(prog, memSummaries)
        var exception = false
        try {
            memAnalysis.inferAll()
        } catch (e: PointerStackEscapingError) {
            // The pointer analysis should throw an exception because stack is escaping
            exception = true
        }
        Assertions.assertEquals(true, exception)
    }
}
