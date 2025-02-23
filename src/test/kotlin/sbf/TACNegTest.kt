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
import log.*
import org.junit.jupiter.api.*
import java.io.ByteArrayOutputStream
import java.io.PrintStream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class TACNegTest {
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

    /** 64-bits unsigned division **/
    @Test
    fun test1() {
        /**
          r2 := -9223372036854775808
          r3 := -5
          r4 := -9223372036854775807
          r2 := neg(r2)
          r3 := neg(r3)
          r4 := neg(r4)
          assert(r2 == -9223372036854775808)
          assert(r3 == 5)
          assert(9223372036854775807)
         */
        val r2 = Value.Reg(SbfRegister.R2_ARG)
        val r3 = Value.Reg(SbfRegister.R3_ARG)
        val r4 = Value.Reg(SbfRegister.R4_ARG)
        val r5 = Value.Reg(SbfRegister.R5_ARG)
        val cfg = MutableSbfCFG("test1")
        val b1 = cfg.getOrInsertBlock(Label.Address(1))
        cfg.setEntry(b1)
        cfg.setExit(b1)

        b1.add(SbfInstruction.Bin(BinOp.MOV, r2, Value.Imm(Long.MIN_VALUE.toULong()), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r3, Value.Imm((-5L).toULong()), true))
        b1.add(SbfInstruction.Bin(BinOp.MOV, r4, Value.Imm(Long.MIN_VALUE.toULong() + 1U), true))
        b1.add(SbfInstruction.Un(UnOp.NEG, r2, true))
        b1.add(SbfInstruction.Un(UnOp.NEG, r3, true))
        b1.add(SbfInstruction.Un(UnOp.NEG, r4, true))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r5, Value.Imm(Long.MIN_VALUE.toULong()), true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r2, r5)))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r3, Value.Imm(5UL))))

        b1.add(SbfInstruction.Bin(BinOp.MOV, r5, Value.Imm(9223372036854775807UL), true))
        b1.add(SbfInstruction.Assert(Condition(CondOp.EQ, r4, r5)))
        b1.add(SbfInstruction.Exit())

        sbfLogger.warn{"$cfg"}
        val tacProg = toTAC(cfg)
        sbfLogger.warn { dumpTAC(tacProg) }
        Assertions.assertEquals(true, verify(tacProg))
    }


}
