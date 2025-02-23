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

import sbf.callgraph.SolanaFunction
import sbf.cfg.*
import sbf.disassembler.*
import sbf.domains.*
import log.*
import org.junit.jupiter.api.*
import java.io.ByteArrayOutputStream
import java.io.PrintStream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class SimplifyBuiltinCallsTest {
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
        sbfLogger.info { "====== TEST 1 =======" }
        /**
         *   r1 := r10 - 24
         *   r2 := r10 - 104
         *   r3 := 32
         *   call memcmp
         **/

        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(24UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(104UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(4UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCMP))
        b1.add(SbfInstruction.Mem(Deref(4, r10, -4), r2, true))
        b1.add(SbfInstruction.Exit())

        sbfLogger.warn { "Before transformation\n$cfg" }
        simplifyMemoryIntrinsics(cfg)
        sbfLogger.warn { "After transformation\n$cfg" }
    }

    @Test
    fun test02() {
        sbfLogger.info { "====== TEST 2 =======" }
        /**
         *   r1 := r10 - 24
         *   r2 := r10 - 104
         *   r3 := 32
         *   r4 := r10 - 4
         *   call sol_memcmp_
         *   r2 := *(u32 *)(r10 -4)
         **/

        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(24UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(104UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(4UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCMP))
        b1.add(SbfInstruction.Mem(Deref(4, r10, -4), r2, true))
        b1.add(SbfInstruction.Exit())

        sbfLogger.warn { "Before transformation\n$cfg" }
        simplifyMemoryIntrinsics(cfg)
        sbfLogger.warn { "After transformation\n$cfg" }
    }

    @Test
    fun test03() {
        sbfLogger.info { "====== TEST 3 =======" }
        /**
         *   r1 := r10 - 24
         *   r2 := r10 - 104
         *   r3 := 32
         *   r4 := r10 - 4
         *   call sol_memcmp_
         *   r2 := *(u32 *)(r10 -4)
         *   r1 := r10 - 24
         *   r2 := r10 - 104
         *   r3 := 32
         *   r4 := r10 - 4
         *   call sol_memcmp_
         *   r2 := *(u32 *)(r10 -4)
         **/

        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(24UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(104UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(4UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCMP))
        b1.add(SbfInstruction.Mem(Deref(4, r10, -4), r2, true))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(24UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(104UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(4UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCMP))
        b1.add(SbfInstruction.Mem(Deref(4, r10, -4), r2, true))

        b1.add(SbfInstruction.Exit())

        sbfLogger.warn { "Before transformation\n$cfg" }
        simplifyMemoryIntrinsics(cfg)
        sbfLogger.warn { "After transformation\n$cfg" }
    }
}
