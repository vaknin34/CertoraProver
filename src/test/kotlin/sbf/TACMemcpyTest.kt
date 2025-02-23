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

import config.ConfigScope
import datastructures.stdcollections.*
import sbf.callgraph.SolanaFunction
import sbf.cfg.*
import sbf.disassembler.SbfRegister
import sbf.disassembler.Label
import sbf.support.UnknownStackContentError
import log.*
import org.junit.jupiter.api.*
import report.*
import java.io.ByteArrayOutputStream
import java.io.PrintStream
import kotlin.collections.listOf

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class TACMemcpyTest {
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
        // r1 and r2 point both to the stack
        /*
           r1 := r10
	       r1 := r1 - 100
	       r2 := r10
	       r2 := r2 - 200

	       *(u64 *) (r2 + 0) := 0
	       *(u64 *) (r2 + 8) := 0
	       *(u64 *) (r2 + 16) := 0
	       *(u64 *) (r2 + 24) := 0
	       r3 := 32
	       call sol_memcpy_(r1,r2,r3)
         */

        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test1")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(100UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(200UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))

        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 8), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 16), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 24), Value.Imm(0UL), false))

        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 16), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 24), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))

        b1.add(SbfInstruction.Exit())
        cfg.normalize()
        cfg.verify(true)
        sbfLogger.warn {"$cfg"}
        val tacProg = toTAC(cfg)
        sbfLogger.warn{dumpTAC(tacProg)}
        Assertions.assertEquals(true, verify(tacProg))
    }


    @Test
    fun test02() {
        // r1 and r2 point both to the stack
        /*
           r1 := r10
	       r1 := r1 - 100
	       r2 := r10
	       r2 := r2 - 200

	       *(u64 *) (r1 + 0) := 1
	       *(u64 *) (r1 + 8) := 1
	       *(u64 *) (r1 + 16) := 1
	       *(u64 *) (r1 + 24) := 1
	       *(u64 *) (r2 + 0) := 0
	       *(u64 *) (r2 + 8) := 0
	       *(u64 *) (r2 + 16) := 0
	       *(u64 *) (r2 + 24) := 0
	       r3 := 32
	       call sol_memcpy_(r1,r2,r3)

	       r3 := *(u64 *) (r1 + 0)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 8)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 16)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 24)
	       assert(r3 == 0)
         */
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test2")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(100UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(200UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), Value.Imm(1UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), Value.Imm(1UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 16), Value.Imm(1UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 24), Value.Imm(1UL), false))

        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 8), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 16), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 24), Value.Imm(0UL), false))

        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 16), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 24), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))

        b1.add(SbfInstruction.Exit())
        cfg.normalize()
        sbfLogger.warn {"$cfg"}
        cfg.verify(true)

        val tacProg = toTAC(cfg)
        sbfLogger.warn{dumpTAC(tacProg)}
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun test03() {
        // memcpy from stack to heap
        /*
           r4 := r10
	       r4 := r4 - 100
	       r2 := r10
	       r2 := r2 - 200

           r3 := 32
           r0 := alloc(r3)
           r1 := r0
           *(u64 *) (r4 + 0) := r1

	       *(u64 *) (r2 + 0) := 0
	       *(u64 *) (r2 + 8) := 0
	       *(u64 *) (r2 + 16) := 0
	       *(u64 *) (r2 + 24) := 0

	       call sol_memcpy_(r1,r2,r3)

	       r3 := *(u64 *) (r1 + 0)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 8)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 16)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 24)
	       assert(r3 == 0)
         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test3")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)
        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(100UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(200UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))

        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r0, true))
        b1.add(SbfInstruction.Mem(Deref(8, r4, 0), r1, false))


        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 8), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 16), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 24), Value.Imm(0UL), false))

        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 16), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 24), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))

        b1.add(SbfInstruction.Exit())
        cfg.normalize()
        cfg.verify(true)
        sbfLogger.info {"$cfg"}
        val tacProg = toTAC(cfg)
        sbfLogger.info{dumpTAC(tacProg)}
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun test04() {
        // memcpy from heap to stack
        /*
           r1 := r10
	       r1 := r1 - 100
	       r4 := r10
	       r4 := r4 - 200

           r3 := 32
           r0 := alloc(r3)
           r2 := r0
           *(u64 *) (r4 + 0) := r2

	       *(u64 *) (r2 + 0) := 0
	       *(u64 *) (r2 + 8) := 0
	       *(u64 *) (r2 + 16) := 0
	       *(u64 *) (r2 + 24) := 0

	       call sol_memcpy_(r1,r2,r3)

	       r3 := *(u64 *) (r1 + 0)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 8)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 16)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 24)
	       assert(r3 == 0)

         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test4")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(100UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(200UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))

        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r0, true))
        b1.add(SbfInstruction.Mem(Deref(8, r4, 0), r2, false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 8), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 16), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 24), Value.Imm(0UL), false))

        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 16), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 24), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))

        b1.add(SbfInstruction.Exit())
        cfg.normalize()
        cfg.verify(true)
        sbfLogger.info {"$cfg"}
        val tacProg = toTAC(cfg)
        sbfLogger.info{dumpTAC(tacProg)}
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun test05() {
        // memcpy from heap to heap
        /*
           r5 := r10
	       r5 := r5 - 100
	       r4 := r10
	       r4 := r4 - 200

           r3 := 32
           r0 := alloc(r3)
           r2 := r0

           r0 := alloc(r3)
           r1 := r0

           *(u64 *) (r1 + 0) := 1
	       *(u64 *) (r1 + 8) := 1
	       *(u64 *) (r1 + 16) := 1
	       *(u64 *) (r1 + 24) := 1

           *(u64 *) (r5 + 0) := r1
           *(u64 *) (r4 + 0) := r2

	       *(u64 *) (r2 + 0) := 0
	       *(u64 *) (r2 + 8) := 0
	       *(u64 *) (r2 + 16) := 0
	       *(u64 *) (r2 + 24) := 0

	       call sol_memcpy_(r1,r2,r3)

	       r3 := *(u64 *) (r1 + 0)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 8)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 16)
	       assert(r3 == 0)
	       r3 := *(u64 *) (r1 + 24)
	       assert(r3 == 0)
         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r5 = Value.Reg(SbfRegister.R5_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test5")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)
        b1.add(SbfInstruction.Bin(BinOp.MOV, r5, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r5, Value.Imm(100UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(200UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))

        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r0, true))

        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r0, true))

        b1.add(SbfInstruction.Mem(Deref(8, r4, 0), r2, false))
        b1.add(SbfInstruction.Mem(Deref(8, r5, 0), r1, false))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), Value.Imm(1UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), Value.Imm(1UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 16), Value.Imm(1UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 24), Value.Imm(1UL), false))

        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 8), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 16), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 24), Value.Imm(0UL), false))

        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 16), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 24), r3, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(0UL))))

        b1.add(SbfInstruction.Exit())
        cfg.normalize()
        cfg.verify(true)
        sbfLogger.info {"$cfg"}
        val tacProg = toTAC(cfg)
        sbfLogger.info{dumpTAC(tacProg)}
        Assertions.assertEquals(true, verify(tacProg))
    }

    @Test
    fun test06() {
        // memcpy from stack to heap with some overlap on the heap part
        /*
           r4 := r10
	       r4 := r4 - 100
	       r2 := r10
	       r2 := r2 - 200

           r3 := 36
           r0 := alloc(r3)
           r1 := r0
           *(u64 *) (r1 + 0) := 5
           r1 := r1 + 4
           *(u64 *) (r4 + 0) := r1

	       *(u64 *) (r2 + 0) := 0
	       *(u64 *) (r2 + 8) := 0
	       *(u64 *) (r2 + 16) := 0
	       *(u64 *) (r2 + 24) := 0

	       call sol_memcpy_(r1,r2,r3)
	       r5 := *(u64 *) (r1 - 4)
           assert(r5 == 5); // this should NOT be proven because r1-4 is partially written by memcpy
                            // if (r1-4) would point to the stack then the pointer analysis would through an exception
                            // when accessing *(r1-4).
         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r5 = Value.Reg(SbfRegister.R5_ARG)
        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test6")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)
        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(100UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(200UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(36UL), true))

        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r0, true))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), Value.Imm(5UL), false))
        b1.add(SbfInstruction.Bin(BinOp.ADD, r1, Value.Imm(4UL), true))
        b1.add(SbfInstruction.Mem(Deref(8, r4, 0), r1, false))

        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 8), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 16), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 24), Value.Imm(0UL), false))

        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Mem(Deref(8, r1, -4), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(5UL))))

        b1.add(SbfInstruction.Exit())
        cfg.normalize()
        cfg.verify(true)
        sbfLogger.warn {"$cfg"}
        val tacProg = toTAC(cfg)
        sbfLogger.warn{dumpTAC(tacProg)}
        Assertions.assertEquals(false, verify(tacProg))
    }

    @Test
    fun test07() {
        // memcpy from heap to stack with overlap on the stack
        /*
           r1 := r10
	       r1 := r1 - 100
	       r4 := r10
	       r4 := r4 - 200

           *(u64 *) (r1 + 0) := 5
           r1:= r1 + 4

           r3 := 32
           r0 := alloc(r3)
           r2 := r0
           *(u64 *) (r4 + 0) := r2

	       *(u64 *) (r2 + 0) := 0
	       *(u64 *) (r2 + 8) := 0
	       *(u64 *) (r2 + 16) := 0
	       *(u64 *) (r2 + 24) := 0

           r5 := *(u64 *) (r1 - 4)
           assert(r5 == 5); // it should be proven

	       call sol_memcpy_(r1,r2,r3)

	       r5 := *(u64 *) (r1 - 4)
           assert(r5 == 5); // it should NOT be proven.
                            // The pointer analysis will complain that we read from some stack offset which becomes inaccessible.
         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r5 = Value.Reg(SbfRegister.R5_ARG)

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test7")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(100UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(200UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), Value.Imm(5UL), false))
        b1.add(SbfInstruction.Bin(BinOp.ADD, r1, Value.Imm(4UL), true))


        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r0, true))
        b1.add(SbfInstruction.Mem(Deref(8, r4, 0), r2, false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 8), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 16), Value.Imm(0UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r2, 24), Value.Imm(0UL), false))

        b1.add(SbfInstruction.Mem(Deref(8, r1, -4), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(5UL))))

        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Mem(Deref(8, r1, -4), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(5UL))))

        b1.add(SbfInstruction.Exit())
        cfg.normalize()
        cfg.verify(true)
        sbfLogger.warn {"$cfg"}
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
    fun test08() {
        // memcpy from summarized heap to stack
        /*

	       r4 := r10
	       r4 := r4 - 200
           r1 := 32
           r0 := alloc
           r2 := r0
           some operation that summarizes the points-to node pointed by r2
           *(u64 *) (r4 + 0) := r2

	       *(u64 *) (r0 + 0) := 5
	       *(u64 *) (r0 + 8) := 6
	       *(u64 *) (r0 + 16) := 7
	       *(u64 *) (r0 + 24) := 8

           r1 := r10
	       r1 := r1 - 100
	       r2 := r0
	       call sol_memcpy_(r1,r2,r3)
	       r5 := *(u64 *) (r1 + 0)
           assert(r5 == 6); // it should be proven.
            r5 := *(u64 *) (r1 + 8)
           assert(r5 == 6); // it should be proven.
            r5 := *(u64 *) (r1 + 16)
           assert(r5 == 7); // it should be proven.
         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r5 = Value.Reg(SbfRegister.R5_ARG)
        val r6 = Value.Reg(SbfRegister.R6)

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test8")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(200UL), true))


        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, Value.Imm(32UL), true))
        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r0, true))
        b1.add(SbfInstruction.Mem(Deref(8, r4, 0), r2, false))

        /// This three instructions cause the summarization of the node pointed by r0
        b1.add(SbfInstruction.Havoc(r5))
        // r4 points somewhere inside the object allocated by alloc, but we don't know where
        b1.add(SbfInstruction.Bin(BinOp.ADD, r2, r5, true))
        // This will summarize the points-to node associated to the allocated object by alloc.
        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), r6, true))


        b1.add(SbfInstruction.Mem(Deref(8, r0, 0), Value.Imm(5UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r0, 8), Value.Imm(6UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r0, 16), Value.Imm(7UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r0, 24), Value.Imm(8UL), false))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(100UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r0, true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(5UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(6UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 16), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(7UL))))

        b1.add(SbfInstruction.Exit())
        cfg.normalize()
        cfg.verify(true)
        sbfLogger.warn {"$cfg"}
        ConfigScope(SolanaConfig.OptimisticPTAOverlaps, true).use {
            val tacProg = toTAC(cfg)
            sbfLogger.warn { dumpTAC(tacProg) }
            Assertions.assertEquals(true, verify(tacProg))
        }

    }

    @Test
    fun test09() {
        // memcpy from summarized heap to stack
        /*

	       r4 := r10
	       r4 := r4 - 200
           r1 := 32
           r0 := alloc
           r2 := r0
           some operation that summarizes the points-to node pointed by r2
           *(u64 *) (r4 + 0) := r2

	       *(u64 *) (r0 + 0) := 5
	       *(u64 *) (r0 + 8) := 6
	       *(u64 *) (r0 + 16) := 7
	       *(u64 *) (r0 + 24) := 8

           r1 := r10
	       r1 := r1 - 100
	       r2 := r0

	       call sol_memcpy_(r1,r2,r3)
	       r2:= r1
	       r1 := r10
	       r1 := r1 - 400
	       call sol_memcpy_(r1,r2,r3)
	       r5 := *(u64 *) (r1 + 0)
           assert(r5 == 5); // it should be proven.
            r5 := *(u64 *) (r1 + 8)
           assert(r5 == 6); // it should be proven.
            r5 := *(u64 *) (r1 + 16)
           assert(r5 == 7); // it should be proven.
         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r5 = Value.Reg(SbfRegister.R5_ARG)
        val r6 = Value.Reg(SbfRegister.R6)

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test9")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(200UL), true))


        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, Value.Imm(32UL), true))
        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r0, true))
        b1.add(SbfInstruction.Mem(Deref(8, r4, 0), r2, false))

        /// This three instructions cause the summarization of the node pointed by r0
        b1.add(SbfInstruction.Havoc(r5))
        // r4 points somewhere inside the object allocated by alloc, but we don't know where
        b1.add(SbfInstruction.Bin(BinOp.ADD, r2, r5, true))
        // This will summarize the points-to node associated to the allocated object by alloc.
        b1.add(SbfInstruction.Mem(Deref(8, r2, 0), r6, true))


        b1.add(SbfInstruction.Mem(Deref(8, r0, 0), Value.Imm(5UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r0, 8), Value.Imm(6UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r0, 16), Value.Imm(7UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r0, 24), Value.Imm(8UL), false))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(32UL), true))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(100UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r0, true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r1, true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(400UL), true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(5UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(6UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 16), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(7UL))))

        b1.add(SbfInstruction.Exit())
        cfg.normalize()
        cfg.verify(true)
        sbfLogger.warn {"$cfg"}
        ConfigScope(SolanaConfig.OptimisticPTAOverlaps, true).use {
            val tacProg = toTAC(cfg)
            sbfLogger.warn { dumpTAC(tacProg) }
            Assertions.assertEquals(true, verify(tacProg))
        }
    }

    @Test
    fun test10() {
        /* This test case does mempcy from stack to EXACT heap, heap to stack, and stack to stack.

           a. Create something on the stack
           b. Memcpy (a) onto exact heap
           c. Memcpy (b) into stack
           d. Access ONE field in (c)  and memcpy ( c) onto stack
           e. Access ALL fields of (d) . They should be same as in (a)

           // (1) store on the stack
	       r4 := r10
	       r4 := r4 - 600
	       *(u64 *) (r4 + 0) := 5
	       *(u64 *) (r4 + 8) := 7

	       // create exact heap
	       r5 := r10
	       r5 := r5 - 500
           r1 := 32
           r0 := alloc
           r1 := r0
           *(u64 *) (r5 + 0) := r1

           r2 := r10
	       r2 := r2 - 600
           r3 := 16
           // (2) memcpy (1) to exact heap
	       call sol_memcpy_(r1,r2,r3)

	       r1 := r10
	       r1 := r1 - 300
	       r2 := *(u64 *) (r5 + 0)
	       r3 := 16
	       // (3) memcpy (2) to stack
	       call sol_memcpy_(r1,r2,r3)
           r6 := *(u64 *) (r1 + 0) // access one field

           r2 := r1
           r1 := r10
	       r1 := r1 - 200
	       r3 := 16
           // (4) memcpy (3) to stack
	       call sol_memcpy_(r1,r2,r3)

           r5 := *(u64 *) (r1 + 0)
           assert(r5 == 5); // it should be proven.
           r5 := *(u64 *) (r1 + 8)
           assert(r5 == 7); // it should be proven.

         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r5 = Value.Reg(SbfRegister.R5_ARG)
        val r6 = Value.Reg(SbfRegister.R6)

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test10")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(600UL), true))
        b1.add(SbfInstruction.Mem(Deref(8, r4, 0), Value.Imm(5UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r4, 8), Value.Imm(7UL), false))


        b1.add(SbfInstruction.Bin(BinOp.MOV, r5, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r5, Value.Imm(500UL), true))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, Value.Imm(32UL), true))
        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r0, true))
        b1.add(SbfInstruction.Mem(Deref(8, r5, 0), r1, false))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(600UL), true))
	    b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(16UL), true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(300UL), true))
        b1.add(SbfInstruction.Mem(Deref(8, r5, 0), r2, true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(16UL), true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))


        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r6, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r6, Value.Imm(5UL))))

	    b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r1, true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(200UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(16UL), true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(5UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(7UL))))

        b1.add(SbfInstruction.Exit())
        cfg.normalize()
        cfg.verify(true)
        sbfLogger.warn {"$cfg"}
        val tacProg = toTAC(cfg)
        sbfLogger.warn{dumpTAC(tacProg)}
        Assertions.assertEquals(true, verify(tacProg))

    }
    @Test
    fun test11() {
        /* This test case does mempcy from stack to SUMMARIZED heap, heap to stack, and stack to stack.

           a. Create something on the stack
           b. Memcpy (a) onto summarized heap
           c. Memcpy (b) into stack
           d. Access ONE field in (c)  and memcpy ( c) onto stack
           e. Access ALL fields of (d) . They should be same as in (a)

           // (1) store on the stack
	       r4 := r10
	       r4 := r4 - 600
	       *(u64 *) (r4 + 0) := 5
	       *(u64 *) (r4 + 8) := 7

	       // create summarized heap
	       r5 := r10
	       r5 := r5 - 500
           r1 := 32
           r0 := alloc
           r1 := r0
           // some operation that summarizes the points-to node pointed by r2
           *(u64 *) (r5 + 0) := r1

           r2 := r10
	       r2 := r2 - 600
           r3 := 16
           // (2) memcpy (1) to summarized heap
	       call sol_memcpy_(r1,r2,r3)

	       r1 := r10
	       r1 := r1 - 300
	       r2 := *(u64 *) (r5 + 0)
	       r3 := 16
	       // (3) memcpy (2) to stack
	       call sol_memcpy_(r1,r2,r3)
           r6 := *(u64 *) (r1 + 0) // access one field

           r2 := r1
           r1 := r10
	       r1 := r1 - 200
	       r3 := 16
           // (4) memcpy (3) to stack
	       call sol_memcpy_(r1,r2,r3)

           r5 := *(u64 *) (r1 + 0)
           assert(r5 == 5); // it should be proven.
           r5 := *(u64 *) (r1 + 8)
           assert(r5 == 7); // it should be proven.

         */

        val r0 = Value.Reg(SbfRegister.R0_RETURN_VALUE)
        val r1 = Value.Reg(SbfRegister.R1_ARG)
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r5 = Value.Reg(SbfRegister.R5_ARG)
        val r6 = Value.Reg(SbfRegister.R6)
        val r7 = Value.Reg(SbfRegister.R7)

        val r10 = Value.Reg(SbfRegister.R10_STACK_POINTER)
        val cfg = MutableSbfCFG("test11")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r4, Value.Imm(600UL), true))
        b1.add(SbfInstruction.Mem(Deref(8, r4, 0), Value.Imm(5UL), false))
        b1.add(SbfInstruction.Mem(Deref(8, r4, 8), Value.Imm(7UL), false))


        b1.add(SbfInstruction.Bin(BinOp.MOV, r5, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r5, Value.Imm(500UL), true))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, Value.Imm(32UL), true))
        b1.add(SbfInstruction.Call(name = "__rust_alloc"))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r0, true))
        b1.add(SbfInstruction.Mem(Deref(8, r5, 0), r1, false))

        /// This three instructions cause the summarization of the node pointed by r0
        b1.add(SbfInstruction.Havoc(r6))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r7, r1, true))
        // r4 points somewhere inside the object allocated by alloc, but we don't know where
        b1.add(SbfInstruction.Bin(BinOp.ADD, r7, r6, true))
        // This will summarize the points-to node associated to the allocated object by alloc.
        b1.add(SbfInstruction.Mem(Deref(8, r7, 0), r6, true))


        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r2, Value.Imm(600UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(16UL), true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(300UL), true))
        b1.add(SbfInstruction.Mem(Deref(8, r5, 0), r2, true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(16UL), true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))


        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r6, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r6, Value.Imm(5UL))))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, r1, true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r1, r10, true))
        b1.add(SbfInstruction.Bin(BinOp.SUB, r1, Value.Imm(200UL), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm(16UL), true))
        b1.add(SolanaFunction.toCallInst(SolanaFunction.SOL_MEMCPY))

        b1.add(SbfInstruction.Mem(Deref(8, r1, 0), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(5UL))))
        b1.add(SbfInstruction.Mem(Deref(8, r1, 8), r5, true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r5, Value.Imm(7UL))))

        b1.add(SbfInstruction.Exit())
        cfg.normalize()
        cfg.verify(true)
        sbfLogger.warn {"$cfg"}
        ConfigScope(SolanaConfig.OptimisticPTAOverlaps, true).use {
            val tacProg = toTAC(cfg)
            sbfLogger.warn { dumpTAC(tacProg) }
            Assertions.assertEquals(true, verify(tacProg))
        }

    }
}
