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
import sbf.analysis.runGlobalInferenceAnalysis
import sbf.callgraph.CVTFunction
import sbf.callgraph.MutableSbfCallGraph
import sbf.cfg.*
import sbf.disassembler.*
import sbf.domains.MemorySummaries
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
class GlobalInferenceAnalysisTest {
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

    /** Mock for the tests **/
    object MockForGlobalsSymbolTable: IGlobalsSymbolTable {
        override fun isGlobalVariable(address: ElfAddress) = (address == 976432L)
        override fun getAsConstantString(
            name: String,
            address: ElfAddress,
            size: Long
        ) = SbfConstantStringGlobalVariable("",0,0, "")
    }

    /**
     * Run the global inference analysis and extracts the type of the dereferenced pointer at
     * [pos]-th instruction in block [label]
     **/
    private fun getTypeFromMemInst(prog: MutableSbfCallGraph, memSummaries: MemorySummaries, label: Label, pos:Int)
        : Pair<SbfInstruction.Mem, SbfType> {
        ConfigScope(SolanaConfig.AggressiveGlobalDetection, true).use {
            val newProg = runGlobalInferenceAnalysis(prog, memSummaries, MockForGlobalsSymbolTable)
            val newCfg = newProg.getCallGraphRootSingleOrFail()
            sbfLogger.warn {"After GIA: $newCfg"}
            val scalarAnalysis =
                ScalarAnalysis(newCfg, newProg.getGlobals(), memSummaries)
            val regTypes = ScalarAnalysisRegisterTypes(scalarAnalysis)
            // Search for the first memory instruction and check that the dereferenced pointer is a global variable
            val bb = newProg.getCallGraphRootSingleOrFail().getBlock(label)
            check(bb != null) { "Cannot find block $label" }
            val locInst = bb.getLocatedInstructions()[pos]
            val inst = locInst.inst
            check(inst is SbfInstruction.Mem) { "$inst is not a memory instruction" }
            val type = regTypes.typeAtInstruction(locInst, inst.access.baseReg.r)
            return inst to type
        }
    }


    @Test
    fun test1() {
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = 976432
                r3 = 1
                r4 = 0
                goto(1)
            }
            bb(1) {
                BinOp.ADD(r4, 2)
                goto(2)
            }
            bb(2) {
                BinOp.ADD(r4, 2)
                goto(3)
            }
            bb(3) {
                BinOp.ADD(r1, r3)
                r1[0] = r4
                exit()
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val prog = MutableSbfCallGraph(listOf(cfg), setOf("entrypoint"), globals)
        sbfLogger.warn {"$cfg"}

        ConfigScope(SolanaConfig.AggressiveGlobalDetection, true).use {
            val newGlobals = runGlobalInferenceAnalysis(prog, memSummaries, MockForGlobalsSymbolTable).getGlobals()
            sbfLogger.warn {"New global map=${newGlobals}\n"}
            Assertions.assertEquals(true,  newGlobals[976432] != null)
        }
    }

    @Test
    fun test2() {
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r3 = 0
                br(CondOp.EQ(r6, 0x0), 1, 2)
            }
            bb(1) {
                r3 = 1
                goto(3)
            }
            bb(2) {
                goto(3)
            }
            // At this point we want to enforce that r3 is num
            bb(3) {
                r1 = 976432
                r4 = 0
                goto(4)
            }
            bb(4) {
                BinOp.ADD(r4, 2)
                r2 = r1
                goto(5)
            }
            bb(5) {
                BinOp.ADD(r4, 2)
                r6 = r2
                r1 = r6
                goto(6)
            }
            bb(6) {
                BinOp.ADD(r1, r3)
                r1[0] = r4
                exit()
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val prog = MutableSbfCallGraph(listOf(cfg), setOf("entrypoint"), globals)
        sbfLogger.warn {"$cfg"}
        ConfigScope(SolanaConfig.AggressiveGlobalDetection, true).use {
            val newGlobals = runGlobalInferenceAnalysis(prog, memSummaries, MockForGlobalsSymbolTable).getGlobals()
            sbfLogger.warn { "New global map=${newGlobals}\n" }
            Assertions.assertEquals(true, newGlobals[976432] != null)
        }
    }

    @Test
    fun test3() {
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = 976432
                r2 = 0
                goto(1)
            }
            bb(1) { // loop header
                br(CondOp.LT(r2, 4), 2, 3)
            }
            bb(2) { //loop body
                r6 = r1
                BinOp.ADD(r6, 8)
                r7 = r6[0]
                // do something with r7
                BinOp.ADD(r2, 1)
                goto(1)
            }
            bb(3) { // loop exit
                exit()
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val prog = MutableSbfCallGraph(listOf(cfg), setOf("entrypoint"), globals)
        sbfLogger.warn {"$cfg"}
        ConfigScope(SolanaConfig.AggressiveGlobalDetection, true).use {
            val newGlobals = runGlobalInferenceAnalysis(prog, memSummaries, MockForGlobalsSymbolTable).getGlobals()
            sbfLogger.warn { "New global map=${newGlobals}\n" }
            Assertions.assertEquals(true, newGlobals[976432] != null)
        }
    }

    @Test
    fun test4() {
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                r1 = 976432
                r2 = 0
                goto(1)
            }
            bb(1) { // loop header
                br(CondOp.LT(r2, 4), 2, 3)
            }
            bb(2) { //loop body
                r6 = r1
                BinOp.ADD(r6, 8)
                r7 = r6[0]
                // do something with r7
                BinOp.ADD(r2, 1)
                goto(4)
            }
            // loop unrolling  r2=1
            bb(4) { // loop header
                br(CondOp.LT(r2, 4), 5, 3)
            }
            bb(5) { //loop body
                r6 = r1
                BinOp.ADD(r6, 8)
                r7 = r6[0]
                // do something with r7
                BinOp.ADD(r2, 1)
                goto(6)
            }
            // loop unrolling r2=2
            bb(6) { // loop header
                br(CondOp.LT(r2, 4), 7, 3)
            }
            bb(7) { //loop body
                r6 = r1
                BinOp.ADD(r6, 8)
                r7 = r6[0]
                // do something with r7
                BinOp.ADD(r2, 1)
                goto(8)
            }
            // loop unrolling r2=3
            bb(8) { // loop header
                br(CondOp.LT(r2, 4), 9, 3)
            }
            bb(9) { //loop body
                r6 = r1
                BinOp.ADD(r6, 8)
                r7 = r6[0]
                // do something with r7
                BinOp.ADD(r2, 1)
                goto(10)
            } // loop unrolling r2=3
            bb(10) { // loop header
                br(CondOp.LT(r2, 4), 11, 3)
            }
            bb(11) { //loop body
                r9 = 0
                assume(CondOp.NE(r9, 0x0)) // assume(false)
            }

            bb(3) { // loop exit
                exit()
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val prog = MutableSbfCallGraph(listOf(cfg), setOf("entrypoint"), globals)
        sbfLogger.warn {"$cfg"}
        ConfigScope(SolanaConfig.AggressiveGlobalDetection, true).use {
            val newGlobals = runGlobalInferenceAnalysis(prog, memSummaries, MockForGlobalsSymbolTable).getGlobals()
            sbfLogger.warn { "New global map=${newGlobals}\n" }
            Assertions.assertEquals(true, newGlobals[976432] != null)
        }
    }

    @Test
    fun test5() {
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                "CVT_nondet_u64"()
                r4 = r0
                r1 = 976432
                BinOp.ADD(r1, r4)
                r3 = r1[0]
                exit()
            }
        }

        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        CVTFunction.addSummaries(memSummaries)
        val prog = MutableSbfCallGraph(listOf(cfg), setOf("entrypoint"), globals)
        sbfLogger.warn {"Before\n$cfg"}
        val (inst, type) = getTypeFromMemInst(prog, memSummaries, Label.Address(0), 4)
        sbfLogger.warn{"Found $inst. The type of the de-referenced pointer is $type"}
        val isGlobal = type is SbfType.PointerType.Global
        Assertions.assertEquals(true, isGlobal)
    }

    @Test
    fun test6() {
        val cfg = SbfTestDSL.makeCFG("test6") {
            bb(0) {
                r1 = 976432
                r7 = r1
                r10[-200] = r7
                br(CondOp.EQ(r2, 0), 1, 2)
            }
            bb(1) {
                goto(3)
            }
            bb(2) {
                goto(3)
            }
            bb(3) {
                goto(4)
            }
            bb(4) {
                goto(5)
            }
            bb(5) {
                goto(6)
            }
            bb(6) {
                goto(7)
            }
            bb(7) {
                goto(8)
            }
            bb(8) {
                goto(9)
            }
            bb(9) {
                goto(10)
            }
            bb(10) {
                goto(11)
            }
            bb(11) {
                r8 = r10[-200]
                r6 = r8
                r7 = r6[0]
                goto(12)
            }
            bb(12) { // loop exit
                exit()
            }
        }
        cfg.verify(true)
        val globals = newGlobalVariableMap()
        val memSummaries = MemorySummaries()
        val prog = MutableSbfCallGraph(listOf(cfg), setOf("test6"), globals)
        sbfLogger.warn {"$cfg"}
        val (inst, type) = getTypeFromMemInst(prog, memSummaries, Label.Address(11), 2)
        sbfLogger.warn{"Found $inst. The type of the de-referenced pointer is $type"}
        val isGlobal = type is SbfType.PointerType.Global
        Assertions.assertEquals(true, isGlobal)
    }

}


