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

import datastructures.stdcollections.*
import sbf.cfg.*
import sbf.disassembler.SbfRegister
import sbf.disassembler.Label
import sbf.support.UnknownStackContentError
import sbf.tac.TACTranslationError
import log.*
import org.junit.jupiter.api.*
import java.io.ByteArrayOutputStream
import java.io.PrintStream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class TACStoresTest {
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
        // r1 points to the stack
        /*
           r1 := r10
	       r1 := r1 - 100
	       *(u64 *) (r1 + 0) := 0
	       *(u64 *) (r1 + 5) := 5
	       r2 := *(u64 *) (r1 + 0)
	       // This is not provable because the second store overlaps with the first store
	       // The pointer analysis will complain that we read from some stack offset which becomes inaccessible.
	       assert(r2 == 0)
         */

        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test1")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(100UL), true))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 4), Value.Imm(5UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r2, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r2, Value.Imm(0UL))))
        b1.add(SbfInstruction.Exit())

        cfg.normalize()
        cfg.verify(true)

        var exception = false
        try {
            toTAC(cfg)
        }
        catch (e: UnknownStackContentError) {
            sbfLogger.warn {"Test failed as expected because $e"}
            exception = true
        }
        Assertions.assertEquals(true, exception)
    }

    @Test
    fun test02() {
        // r1 points to the heap
        /*
           r2 := r10
	       r2 := r2 - 100

	       r1 := 32
	       malloc()
	       r1 := r0
	       *(u64 *) (r2 + 0) := r1
	       *(u64 *) (r1 + 0) := 0
	       *(u64 *) (r1 + 8) := 5
	       r3 := *(u64 *) (r1 + 0)
	       assert(r3 == 0)
         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test2")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(100UL), true))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, Value.Imm(32UL), true))
        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r0, true))

        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), r1, false))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), Value.Imm(5UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Exit())

        cfg.normalize()
        cfg.verify(true)

        val tacProg = toTAC(cfg)
        sbfLogger.warn{dumpTAC(tacProg)}
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun test03() {
        // r1 points to the heap
        /*
           r2 := r10
	       r2 := r2 - 100

	       r1 := 32
	       malloc()
	       r1 := r0
	       *(u64 *) (r2 + 0) := r1

	       *(u64 *) (r1 + 0) := 0
	       *(u64 *) (r1 + 4) := 5
	       r3 := *(u64 *) (r1 + 0)
	       // This is not provable because the second store overlaps with the first store
	       assert(r3 == 0)
         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test3")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(100UL), true))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, Value.Imm(32UL), true))
        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r0, true))

        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), r1, false))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 4), Value.Imm(5UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Exit())

        cfg.normalize()
        cfg.verify(true)

        val tacProg = toTAC(cfg)
        sbfLogger.warn{dumpTAC(tacProg)}
        Assertions.assertEquals(false, verify(tacProg))
    }

    @Test
    fun test04() {
        // r1 points to the heap but the node is summarized
        /*
           r2 := r10
	       r2 := r2 - 100

	       r1 := 32
	       malloc()
	       r1 := r0
	       some operation that summarizes the points-to node pointed by r1
	       *(u64 *) (r2 + 0) := r1

	       *(u64 *) (r1 + 0) := 0
	       *(u64 *) (r1 + 4) := 5
	       r3 := *(u64 *) (r1 + 0)
	       // This is not provable because the second store overlaps with the first store
	       // Because the verifier cannot reason precisely about overlaps it should throw an exception.
	       assert(r3 == 0)
         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r5 = Value.Reg(SbfRegister.R5_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test4")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(100UL), true))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, Value.Imm(32UL), true))
        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r0, true))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), r1, false))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r1, true))
        b1.add(SbfInstruction.Havoc(r5))
        // r4 points somewhere inside the object allocated by alloc, but we don't know where
        b1.add(SbfInstruction.Bin(BinOp.ADD, r4, r5, true))
        // This will summarize the points-to node associated to the allocated object by alloc.
        b1.add(SbfInstruction.Mem(Deref(8, r4, 0), Value.Imm(10UL), false))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 4), Value.Imm(5UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Exit())

        cfg.normalize()
        cfg.verify(true)

        var exception = false
        try {
            toTAC(cfg)
        }
        catch (e: TACTranslationError) {
            sbfLogger.warn {"Test failed as expected because $e"}
            exception = true
        }
        Assertions.assertEquals(true, exception)
    }
}
