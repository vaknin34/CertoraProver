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
import sbf.analysis.NPAnalysis
import sbf.cfg.*
import sbf.disassembler.*
import sbf.domains.MemorySummaries
import sbf.testing.SbfTestDSL
import log.*
import org.junit.jupiter.api.*
import java.io.ByteArrayOutputStream
import java.io.PrintStream

@TestInstance(TestInstance.Lifecycle.PER_CLASS)
@TestMethodOrder(MethodOrderer.OrderAnnotation::class)
@Order(1)
class RemoveCFGDiamondsTest {
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

    private fun checkSelect(inst: SbfInstruction.Select, lhs: Value.Reg, cond: Condition, trueVal: Value, falseVal: Value) =
        inst.dst == lhs && inst.cond == cond && inst.trueVal == trueVal && inst.falseVal == falseVal

    /** Check only the first select instruction found in [cfg] **/
    private fun checkFirstSelect(cfg: SbfCFG, lhs: Value.Reg, cond: Condition, trueVal: Value, falseVal: Value): Boolean {
        for (inst in cfg.getEntry().getInstructions()) {
            if (inst is SbfInstruction.Select) {
                return checkSelect(inst, lhs, cond, trueVal, falseVal)
            }
        }
        return false
    }

    private fun numOfSelect(cfg: SbfCFG): Int {
        var n = 0
        for (block in cfg.getBlocks().values) {
            for (inst in block.getInstructions()) {
                if (inst is SbfInstruction.Select) {
                    n++
                }
            }
        }
        return n
    }

    @Test
    fun test1() {
        /**
         *    ```
         *       r0 := sol_memcmp()
         *       r1 := r0
         *       r0 := 1
         *       if (r1 != 0) {
         *          r0 :=0
         *       }
         *       assume(r0 == 0)
         *       assert(...) // needed to run the backward analysis
         *    ```
         *
         *    This examples shows that it is crucial to remove the dead assignment `r0 := 1`
         *
         *    ```
    	 *       r0 := sol_memcmp
    	 *       r1 := r0
    	 *       r0 := 1   <--- dead assignment
     	 *       r0 := select(r1 != 0, 1, 0)
    	 *       goto 2
         *    2:
    	 *       assume(r0 == 0)
    	 *       assert(...)
         *    ```
         *
    	 *    Otherwise, after we replace select with assume:
         *
         *    ```
     	 *       r0 := sol_memcmp
    	 *       r1 := r0
    	 *       r0 := 1   <---  dead assignment
    	 *       assume(r1 == 0)
    	 *       goto 2
         *    2:
    	 *       assume(r0 == 0)
    	 *       assert(...)
         *    ```
         *
         *    A backward analysis would incorrectly infer that the precondition at the entry block is bottom
         *    because `assume(r0 == 0)` and `r0 := 1`
        **/
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(0) {
                "__sol_memcmp"()
                r1 = r0
                r0 = 1
                br(CondOp.NE(r1, 0x0), 1, 2)
            }
            bb(1) {
                r0  = 0
                goto(2)
            }
            bb(2) {
                assume(CondOp.EQ(r0, 0x0))
                assert(CondOp.EQ(r2, 0x0))
                exit()
            }
        }

        sbfLogger.warn {"$cfg"}
        cfg.simplify(newGlobalVariableMap())
        ConfigScope(SolanaConfig.EnableRemovalOfCFGDiamonds, true).use {removeCFGDiamonds(cfg)}
        sbfLogger.warn {"After removing diamonds: $cfg"}

        val np1 = NPAnalysis(cfg, newGlobalVariableMap(), MemorySummaries())
        lowerSelectToAssume(cfg, np1)
        sbfLogger.warn {"After lowering select instructions into assumes: $cfg"}
        val np2 = NPAnalysis(cfg, newGlobalVariableMap(), MemorySummaries())
        val preconditions = np2.getPreconditionsAtEntry(Label.Address(0))
        check(preconditions != null)
        Assertions.assertEquals(false, preconditions.isBottom())
    }

    @Test
    fun test2() {
        /**
         * ```
         * b1:
         *   r4 := 0
         *   r1 := *(u64 *) (r1 + 24)
         *   r3 := *(u64 *) (r10 + -752)
         *   if (r1 != r3) then goto b2 else goto b3
         * b2:
         *    r4 := 1
         *    goto b3
         * b3:
         *   exit
         *```
         **/
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(1) {
                r4 = 0
                r1 = r10[-24]
                r3 = r10[-752]
                br(CondOp.NE(r1, r3), 2, 3)
            }
            bb(2) {
                r4  = 1
                goto(3)
            }
            bb(3) {
                exit()
            }
        }

        sbfLogger.warn {"$cfg"}
        cfg.simplify(newGlobalVariableMap())
        ConfigScope(SolanaConfig.EnableRemovalOfCFGDiamonds, true).use {removeCFGDiamonds(cfg) }
        sbfLogger.warn {"After removing diamonds: $cfg"}
        Assertions.assertEquals(true,
            checkFirstSelect(cfg,
                Value.Reg(SbfRegister.R4_ARG), Condition(CondOp.EQ, Value.Reg(SbfRegister.R1_ARG), Value.Reg(SbfRegister.R3_ARG)), Value.Imm(0UL), Value.Imm(1UL))
            )
    }

    @Test
    fun test3() {
        /**
         * ```
         * b1:
         *   r4 := 0
         *   r1 := *(u64 *) (r1 + 24)
         *   r3 := *(u64 *) (r10 + -752)
         *   if (r1 == r3) then goto b2 else goto b3
         * b2:
         *    r4 := 1
         *    goto b3
         * b3:
         *   exit
         *```
         **/
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(1) {
                r4 = 0
                r1 = r10[-24]
                r3 = r10[-752]
                br(CondOp.EQ(r1, r3), 2, 3)
            }
            bb(2) {
                r4  = 1
                goto(3)
            }
            bb(3) {
                exit()
            }
        }

        sbfLogger.warn {"$cfg"}
        cfg.simplify(newGlobalVariableMap())
        ConfigScope(SolanaConfig.EnableRemovalOfCFGDiamonds, true).use {removeCFGDiamonds(cfg)}
        sbfLogger.warn {"After removing diamonds: $cfg"}
        Assertions.assertEquals(true,
            checkFirstSelect(cfg,
                Value.Reg(SbfRegister.R4_ARG), Condition(CondOp.NE, Value.Reg(SbfRegister.R1_ARG), Value.Reg(SbfRegister.R3_ARG)), Value.Imm(0UL), Value.Imm(1UL))
        )
    }

    @Test
    fun test4() {
        /**
         * ```
         * b1:
         *   r4 := 1
         *   r4 := 0
         *   *(u64 *) (r1 + 24) := r4
         *   if (r1 == r3) then goto b2 else goto b3
         * b2:
         *    r4 := 1
         *    goto b3
         * b3:
         *   exit
         *```
         **/
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(1) {
                r4 = 1
                r4 = 0
                r10[-24] = r4
                br(CondOp.EQ(r1, r3), 2, 3)
            }
            bb(2) {
                r4  = 1
                goto(3)
            }
            bb(3) {
                exit()
            }
        }

        sbfLogger.warn {"$cfg"}
        cfg.simplify(newGlobalVariableMap())
        ConfigScope(SolanaConfig.EnableRemovalOfCFGDiamonds, true).use {removeCFGDiamonds(cfg)}
        sbfLogger.warn {"After removing diamonds: $cfg"}
        Assertions.assertEquals(true,
            checkFirstSelect(cfg,
                Value.Reg(SbfRegister.R4_ARG), Condition(CondOp.NE, Value.Reg(SbfRegister.R1_ARG), Value.Reg(SbfRegister.R3_ARG)), Value.Reg(SbfRegister.R4_ARG), Value.Imm(1UL))
        )
    }

    @Test
    fun test5() {
        /**
         * ```
         * b1:
         *   r4 := 1
         *   r4 := 0
         *   if (r1 == r3) then goto b2 else goto b3
         * b2:
         *    *(u64 *) (r1 + 24) := r4
         *    r4 := 1
         *    goto b3
         * b3:
         *   exit
         *```
         **/
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(1) {
                r4 = 1
                r4 = 0
                br(CondOp.EQ(r1, r3), 2, 3)
            }
            bb(2) {
                r10[-200] = r4
                r4  = 1
                goto(3)
            }
            bb(3) {
                exit()
            }
        }

        sbfLogger.warn {"$cfg"}
        cfg.simplify(newGlobalVariableMap())
        ConfigScope(SolanaConfig.EnableRemovalOfCFGDiamonds, true).use {removeCFGDiamonds(cfg)}
        sbfLogger.warn {"After removing diamonds: $cfg"}
        Assertions.assertEquals(false,
            cfg.getBlocks().values.any {
                it.getInstructions().any { it is SbfInstruction.Select }
            }
        )
    }

    @Test
    fun test6() {
        /**
         * ```
         * b1:
         *   r1 := select(r7 ule r4, 0, 1)
         *   r5 := select(r6 ule r3, 0, 1)
         *   if (r3 == r6) then goto b2 else goto b3
         * b2:
         *    r1 := r5
         *    goto b3
         * b3:
         *   exit
         *```
         **/
        val cfg = SbfTestDSL.makeCFG("entrypoint") {
            bb(1) {
                select(r1, CondOp.LE(r7, r4), 0, 1)
                select(r5, CondOp.LE(r6, r3), 0, 1)
                br(CondOp.EQ(r3, r6), 2, 3)
            }
            bb(2) {
                r1  = r5
                goto(3)
            }
            bb(3) {
                exit()
            }
        }

        sbfLogger.warn {"$cfg"}
        ConfigScope(SolanaConfig.EnableRemovalOfCFGDiamonds, true).use {removeCFGDiamonds(cfg)}
        sbfLogger.warn {"After removing diamonds: $cfg"}
        Assertions.assertEquals(true, numOfSelect(cfg) == 3)
    }


}
